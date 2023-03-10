from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses, names,
    get_random_degree, mutate_normal, shuffle_normal, get_open_file,
    write_patch)
from randomtools.utils import (
    map_to_lorom, map_from_lorom,
    classproperty, cached_property, clached_property,
    read_lines_nocomment, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_flags, get_activated_codes,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)
from randomtools.itemrouter import ItemRouter, ItemRouterException

from collections import defaultdict, Counter
from copy import deepcopy
from os import path
import re
from string import ascii_letters, digits, punctuation
from traceback import format_exc


VERSION = '3.0b'
ALL_OBJECTS = None
DEBUG_MODE = False


def hexify(s):
    return '-'.join('{0:0>2X}'.format(c) for c in s)


EVENT_PATCHES = [
    'skip_tutorial'
]


class ReadExtraMixin(object):
    end_pointer = None

    def read_extra(self, filename=None, pointer=None):
        if filename is None:
            filename = self.filename

        if pointer is None:
            if hasattr(self, 'additional_conclude_pointer'):
                pointer = self.additional_conclude_pointer
            else:
                pointer = self.pointer + self.specs.total_size

        nexts = [o for o in self.every if o.pointer > self.pointer]
        if nexts:
            next_obj = min(nexts, key=lambda o2: o2.pointer)
            end_pointer = next_obj.pointer
        elif self.end_pointer is not None:
            end_pointer = self.end_pointer
        else:
            end_pointer = pointer

        f = get_open_file(filename)
        f.seek(pointer)
        assert end_pointer >= pointer
        self.extra_pointer = pointer
        self.extra = f.read(end_pointer-pointer)

    def write_extra(self, filename=None, pointer=None):
        if filename is None:
            filename = self.filename

        if pointer is None:
            if not hasattr(self, 'extra_pointer'):
                self.read_extra(filename=filename)
            pointer = self.extra_pointer

        f = get_open_file(filename)
        f.seek(pointer)
        f.write(self.extra)


class AdditionalPropertiesMixin(ReadExtraMixin):
    _pre_read = []

    def read_data(self, filename=None, pointer=None):
        assert self not in self._pre_read
        super(AdditionalPropertiesMixin, self).read_data(filename, pointer)
        filename = filename or self.filename

        offset = self.pointer + self.specs.total_size
        self.additional_addresses = {}
        self.additional_properties = {}
        bitnames = [bn for bns in self.additional_bitnames
                    for bn in self.specs.bitnames[bns]]

        f = get_open_file(filename)
        for bitname in bitnames:
            if self.get_bit(bitname):
                self.additional_addresses[bitname] = offset
                f.seek(offset)
                value = int.from_bytes(f.read(2), byteorder='little')
                self.additional_properties[bitname] = value
                offset += 2
        self.additional_conclude_pointer = offset

        prevs = [i for i in self._pre_read if i.pointer < self.pointer]
        nexts = [i for i in self._pre_read if i.pointer > self.pointer]
        if prevs:
            p = max(prevs, key=lambda p2: p2.pointer)
            assert self.pointer >= max(
                [p.pointer] + sorted(p.additional_addresses.values()))+2

        if nexts:
            n = min(nexts, key=lambda n2: n2.pointer)
            assert max([self.pointer] +
                       self.additional_addresses.values())+2 <= n.pointer

        self._pre_read.append(self)

    def write_data(self, filename=None, pointer=None):
        super(AdditionalPropertiesMixin, self).write_data(filename, pointer)
        filename = filename or self.filename

        bitnames = [bn for bns in self.additional_bitnames
                    for bn in self.specs.bitnames[bns]]

        f = get_open_file(filename)
        for bitname in bitnames:
            if self.get_bit(bitname):
                offset = self.additional_addresses[bitname]
                value = self.additional_properties[bitname]
                f.seek(offset)
                f.write(value.to_bytes(length=2, byteorder='little'))
                offset += 2
            else:
                assert bitname not in self.additional_addresses
                assert bitname not in self.additional_properties
        self.write_extra()


class PriceMixin(object):
    def price_clean(self):
        power = 0
        price = self.price
        assert price < 65536
        price = price * 2
        while 0 < price < 10000:
            price *= 10
            power += 1
        price = int(round(price, -3))
        price /= (10**power)
        price = price / 2
        assert price <= 65500
        if price > 10 and price % 10 == 0 and int(VERSION[0]) % 2 == 1:
            price = price - 1
        self.price = int(round(price))


class AncientChestMixin(object):
    flag = 't'
    custom_random_enable = True

    @property
    def item(self):
        return ItemObject.get(self.item_index)

    @property
    def name(self):
        return self.item.name

    @property
    def distribution(self):
        return [ac.old_data['item_index'] for ac in self.every]

    @property
    def equal_distribution(self):
        return sorted(set(self.distribution))

    def mutate(self):
        if random.random() <= self.random_degree:
            candidates = list(self.equal_distribution)
        else:
            candidates = list(self.distribution)
        candidates.append(None)
        while random.random() < (self.random_degree / 2):
            candidates.append(None)
        self.reseed(salt='ac_chest')
        chosen = random.choice(candidates)
        if chosen is None:
            candidates = [i.index for i in ItemObject.every if i.rank > 0
                          and (i.get_bit('equipable') is False
                               or not i.equipability
                               or i.get_bit('ban_ancient_cave') is True)]
            candidates.append(0x36)  # dual blade
            candidates = sorted(set(candidates))
            chosen = random.choice(candidates)
        self.item_index = chosen


class AncientChest1Object(AncientChestMixin, TableObject): pass
class AncientChest2Object(AncientChestMixin, TableObject): pass


class CapsuleObject(ReadExtraMixin, TableObject):
    flag = 'p'
    flag_description = 'capsule monsters'
    custom_random_enable = True

    intershuffle_attributes = [
        ('hp', 'hp_factor'),
        'attack',
        'defense',
        ('strength', 'strength_factor'),
        ('agility', 'agility_factor'),
        ('intelligence', 'intelligence_factor'),
        ('guts', 'guts_factor'),
        ('magic_resistance', 'magic_resistance_factor'),
        ]
    mutate_attributes = {
        'hp': None,
        'hp_factor': None,
        'attack': None,
        'defense': None,
        'strength': None,
        'strength_factor': None,
        'agility': None,
        'agility_factor': None,
        'intelligence': None,
        'intelligence_factor': None,
        'guts': None,
        'guts_factor': None,
        'magic_resistance': None,
        'magic_resistance_factor': None,
    }

    @property
    def name(self):
        return self.name_text.decode('utf8').strip()

    @property
    def rank(self):
        return self.capsule_class

    @staticmethod
    def reorder_capsules(ordering):
        sprites = [CapSpritePTRObject.get(i).sprite_pointer
                   for i in ordering]
        palettes = [CapPaletteObject.get(i).get_all_colors()
                    for i in ordering]
        pointers = [CapsuleObject.get(i).pointer for i in ordering]
        start = CapsuleObject.specs.pointer
        for i, (pointer, sprite, palette) in enumerate(
                zip(pointers, sprites, palettes)):
            c = CapsuleObject.get(i)
            f = get_open_file(get_outfile())
            f.seek(start + (2*c.index))
            f.write((pointer-start).to_bytes(length=2, byteorder='little'))
            c.pointer = pointer
            c.read_data(filename=get_outfile(), pointer=c.pointer)
            CapSpritePTRObject.get(i).sprite_pointer = sprite
            CapPaletteObject.get(i).set_all_colors(palette)

    @classmethod
    def full_randomize(cls):
        CapsuleObject.end_pointer = addresses.capsule_end
        CapsuleObject.class_reseed('full')
        ordering = []
        for c in CapsuleObject.every:
            candidates = [c2.index for c2 in CapsuleObject.every
                          if c2.capsule_class == c.capsule_class]
            candidates = [c2 for c2 in candidates if c2 not in ordering]
            ordering.append(random.choice(candidates))
        CapsuleObject.reorder_capsules(ordering)
        super(CapsuleObject, cls).full_randomize()

    def mutate(self):
        super(CapsuleObject, self).mutate()
        #self.mutate_skills()

    def mutate_skills(self):
        near_alignments = [self.alignment]
        if self.capsule_class > 1:
            near_alignments.append(CapsuleObject.get(self.index-1).alignment)
        if self.capsule_class < 5:
            near_alignments.append(CapsuleObject.get(self.index+1).alignment)
        skill_ranks = {}
        for c in CapsuleObject.every:
            related = (c.alignment == self.alignment or
                       (c.index / 5) == (self.index / 5))
            near = (abs(c.capsule_class - self.capsule_class) <= 1
                    and c.alignment in near_alignments)
            if (related or near):
                for key in ['start_skills', 'upgrade_skills']:
                    for skill in c.old_data[key]:
                        if skill == 0:
                            continue
                        value = c.capsule_class
                        if key == 'upgrade_skills':
                            value += 0.5
                        if (skill not in skill_ranks
                                or skill_ranks[skill] > value):
                            skill_ranks[skill] = value

        skills = sorted(skill_ranks,
                        key=lambda s: (skill_ranks[s], random.random(), s))

        done = set([])
        ordering = range(6)
        random.shuffle(ordering)
        for i in ordering:
            s = (self.start_skills + self.upgrade_skills)[i]
            if s == 0:
                continue
            while True:
                index = skills.index(s)
                index = mutate_normal(index, 0, len(skills)-1, wide=True,
                                      random_degree=self.random_degree)
                new_skill = skills[index]
                if new_skill not in done:
                    done.add(new_skill)
                    if i <= 2:
                        self.start_skills[i] = new_skill
                    else:
                        self.upgrade_skills[i%3] = new_skill
                    break

    def cleanup(self):
        # for use in reading capsule monster AI scripts
        # skill uses seem to be in the format: 3E XX
        # but it's not consistent in the case of Myconido, for example
        self.read_extra()


class CapSpritePTRObject(TableObject): pass


class FormationObject(TableObject):
    @property
    def name(self):
        ncs = ''
        for key in sorted(self.name_counts):
            count = self.name_counts[key]
            nc = '{0} x{1}'.format(key, count)
            if ncs:
                ncs = ', '.join([ncs, nc])
            else:
                ncs = nc
            assert count > 0
        return ncs

    @cached_property
    def name_counts(self):
        names = [MonsterObject.get(i).name
                 for i in self.monster_indexes if i != 0xFF]
        return Counter(names)

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)

        base_pointer = self.specs.pointer
        assert base_pointer == 0xbc53d
        formation_pointer = base_pointer + self.reference_pointer
        f = get_open_file(get_outfile())
        f.seek(formation_pointer)
        self.monster_indexes = [int(c) for c in f.read(6)]
        self.monster_coordinates = []
        for _ in range(6):
            x = ord(f.read(1))
            y = ord(f.read(1))
            self.monster_coordinates.append((x, y))
        self.unknown = f.read(12)


class CapPaletteObject(TableObject):
    def get_all_colors(self):
        colors = []
        for i in range(0x10):
            c = getattr(self, 'color%X' % i)
            colors.append(c)
        return colors

    def set_all_colors(self, colors):
        for i, c in enumerate(colors):
            setattr(self, 'color%X' % i, c)


class ChestObject(TableObject):
    flag = 't'
    flag_description = 'treasure chests'
    custom_random_enable = True

    def __repr__(self):
        s = 'CHEST {0:0>2X}: {1:0>6x}-{2:0>3X} {3}'.format(
            self.index, self.pointer, self.item_index,
            self.item.name.decode('ascii'))
        return s

    @property
    def item_index(self):
        return (
            self.get_bit('item_high_bit') << 8) | self.item_low_byte

    @property
    def item(self):
        return ItemObject.get(self.item_index)

    def set_item(self, item):
        if isinstance(item, ItemObject):
            item = item.index
        if item & 0x100:
            self.set_bit('item_high_bit', True)
        else:
            self.set_bit('item_high_bit', False)
        self.item_low_byte = item & 0xFF

    def mutate(self):
        i = self.item.get_similar()
        self.set_item(i)

    @classmethod
    def full_randomize(cls):
        ChestObject.class_reseed('ac')
        candidates = [i for i in ItemObject.every
                      if i.equipability and i.get_bit('equipable')]
        shuffled = shuffle_normal(
            candidates, wide=True, random_degree=ChestObject.random_degree)

        bits = [c.get_bit('ban_ancient_cave') for c in candidates]
        assert len(bits) == len(shuffled)
        for b, s in zip(bits, shuffled):
            if random.random() < (ChestObject.random_degree ** 1.5):
                b = random.choice(bits)
            s.set_bit('ban_ancient_cave', b)

        super(ChestObject, cls).full_randomize()


class BlueChestObject(TableObject):
    flag = 't'
    custom_random_enable = True

    @property
    def item(self):
        return ItemObject.get(self.item_index)

    @property
    def name(self):
        return self.item.name

    @classmethod
    def mutate_all(cls):
        candidates = [i for i in ItemObject.every
                      if i.equipability and i.get_bit('equipable')
                      and i.rank >= 0]
        done = set([])
        for b in BlueChestObject.every:
            b.reseed(salt='mut')
            while True:
                i = b.item.get_similar(
                    candidates=candidates,
                    random_degree=BlueChestObject.random_degree)
                if i in done:
                    continue
                b.item_index = i.index
                done.add(i)
                break

    def cleanup(self):
        self.item.set_bit('ban_ancient_cave', True)


class SpellObject(PriceMixin, TableObject):
    flag = 'l'
    flag_description = 'learnable spells'
    custom_random_enable = 'i'

    mutate_attributes = {
        'price': (1, 65500),
        'mp_cost': None,
    }

    @property
    def name(self):
        return self.name_text.decode('utf8').strip()

    @classproperty
    def after_order(self):
        if 'c' in get_flags():
            return [CharacterObject]
        return []

    @staticmethod
    def intershuffle():
        SpellObject.class_reseed('inter')
        old_casters = []
        for i in range(7):
            mask = (1 << i)
            charmasks = [s.characters & mask for s in SpellObject.every]
            if not any(charmasks):
                continue
            old_casters.append(i)
            num_learnable = len([c for c in charmasks if c])
            num_learnable = mutate_normal(
                num_learnable, 1, len(charmasks), wide=True,
                random_degree=SpellObject.random_degree)
            charmasks = [mask if i < num_learnable else 0
                         for i in range(len(charmasks))]
            random.shuffle(charmasks)
            for s, charmask in zip(SpellObject.every, charmasks):
                if s.characters & mask:
                    s.characters = s.characters ^ mask
                assert not s.characters & mask
                s.characters |= charmask

        old_spells = {}
        for i in old_casters:
            mask = (1 << i)
            spells = [bool(s.characters & mask) for s in SpellObject.every]
            old_spells[i] = spells

        for s in SpellObject.every:
            s.characters = 0

        new_casters = [i for i in range(7)
                       if CharacterObject.get(i).is_caster]
        random.shuffle(new_casters)
        for a, b in zip(old_casters, new_casters):
            mask = (1 << b)
            spells = old_spells[a]
            for truth, s in zip(spells, SpellObject.every):
                if truth:
                    s.characters |= mask

        for s in SpellObject.every:
            if not s.characters:
                mask = (1 << random.choice(new_casters))
                s.characters |= mask

    @property
    def rank(self):
        return self.old_data['price']

    def cleanup(self):
        if self.index == 0x26:
            self.set_bit('maxim', True)
            self.mp_cost = 0
        if 's' not in get_flags() and 'l' not in get_flags():
            return
        self.price_clean()


class CharGrowthObject(TableObject):
    flag = 'c'
    custom_random_enable = True

    mutate_attributes = {
        'hp': None,
        'mp': None,
        'str': None,
        'agl': None,
        'int': None,
        'gut': None,
        'mgr': None,
        }

    @classproperty
    def after_order(self):
        return [CharacterObject]

    @staticmethod
    def get_character(character_index):
        if not isinstance(character_index, int):
            character_index = character_index.index
        return [cg for cg in CharGrowthObject.every
                if cg.index / 13 == character_index]

    @property
    def name(self):
        return CharacterObject.get(self.index/13).name

    def mutate(self):
        super(CharGrowthObject, self).mutate()


class CharacterObject(TableObject):
    flag = 'c'
    flag_description = 'characters'
    custom_random_enable = True

    @property
    def name(self):
        return {0: 'Maxim',
                1: 'Selan',
                2: 'Guy',
                3: 'Artea',
                4: 'Tia',
                5: 'Dekar',
                6: 'Lexis'}[self.index]

    @staticmethod
    def intershuffle():
        CharacterObject.class_reseed('inter')
        indexes = [c.index for c in CharacterObject.every]

        for key in CharGrowthObject.mutate_attributes:
            ordering = list(indexes)
            random.shuffle(ordering)
            for (ai, bi) in zip(indexes, ordering):
                aa = CharGrowthObject.get_character(ai)
                bb = CharGrowthObject.get_character(bi)
                for (a, b) in zip(aa, bb):
                    bv = b.old_data[key]
                    setattr(a, key, bv)

                a = CharacterObject.get(ai)
                b = CharacterObject.get(bi)
                bv = b.old_data[key]
                setattr(a, key, bv)

    @property
    def growths(self):
        return CharGrowthObject.get_character(self.index)

    @property
    def growth_mp(self):
        return sum([cg.mp for cg in self.growths])

    @property
    def mp_rank(self):
        cs = sorted(CharacterObject.every,
                    key=lambda c: (c.growth_mp, c.index))
        return cs.index(self)

    @property
    def is_caster(self):
        return self.mp_rank >= 2


class MonsterObject(TableObject):
    flag = 'm'
    flag_description = 'monsters'
    custom_random_enable = True

    intershuffle_attributes = [
        'hp', 'attack', 'defense', 'agility', 'intelligence',
        'guts', 'magic_resistance', 'xp', 'gold']

    mutate_attributes = {
        'level': None,
        'hp': None,
        'attack': None,
        'defense': None,
        'agility': None,
        'intelligence': None,
        'guts': None,
        'magic_resistance': None,
        'xp': None,
        'gold': None,
    }

    @property
    def intershuffle_valid(self):
        return (self.rank >= 0 and not 0xA7 <= self.index <= 0xAA
                and self.index not in [0xdf])

    @property
    def name(self):
        return self.name_text.decode('utf8').strip()

    @property
    def has_drop(self):
        return self.misc == 3

    @property
    def drop(self):
        return ItemObject.get(self.drop_index)

    @property
    def drop_index(self):
        return self.drop_data & 0x1FF

    @property
    def drop_rate(self):
        return self.drop_data >> 9

    @property
    def is_boss(self):
        return self.index >= 0xBC

    @property
    def rank(self):
        if hasattr(self, '_rank'):
            return self._rank
        rankdict = {}
        if self.index in rankdict:
            self._rank = rankdict[self.index]
        elif self.is_boss:
            self._rank = self.level * (self.hp ** 2)
        else:
            assert self.level * self.hp * self.xp != 0
            self._rank = self.level * self.hp * self.xp
        return self.rank

    @classmethod
    def intershuffle(cls):
        MonsterObject.class_reseed('inter')
        super(MonsterObject, cls).intershuffle(
            candidates=[m for m in MonsterObject.every if not m.is_boss])
        super(MonsterObject, cls).intershuffle(
            candidates=[m for m in MonsterObject.every if m.is_boss])

    def set_drop(self, item):
        if isinstance(item, ItemObject):
            item = item.index
        new_data = self.drop_data & 0xFE00
        self.drop_data = new_data | item

    def set_drop_rate(self, rate):
        new_data = self.drop_data & 0x1FF
        self.drop_data = new_data | (rate << 9)

    def read_data(self, filename=None, pointer=None):
        super(MonsterObject, self).read_data(filename, pointer)
        filename = filename or self.filename
        if self.has_drop:
            f = get_open_file(filename)
            f.seek(self.pointer+self.specs.total_size)
            self.drop_data = int.from_bytes(f.read(2), byteorder='little')

    def write_data(self, filename=None, pointer=None):
        super(MonsterObject, self).write_data(filename, pointer)
        filename = filename or self.filename
        if self.has_drop:
            f = get_open_file(filename)
            f.seek(self.pointer+self.specs.total_size)
            f.write(self.drop_data.to_bytes(length=2, byteorder='little'))

    def mutate(self):
        super(MonsterObject, self).mutate()
        if self.has_drop:
            i = self.drop.get_similar()
            self.set_drop(i)

    def cleanup(self):
        if self.is_boss:
            for attr in self.mutate_attributes:
                if getattr(self, attr) < self.old_data[attr]:
                    setattr(self, attr, self.old_data[attr])

        if 'easymodo' in get_activated_codes():
            for attr in ['hp', 'attack', 'defense', 'agility', 'intelligence',
                         'guts', 'magic_resistance']:
                setattr(self, attr, 1)


class ItemObject(AdditionalPropertiesMixin, PriceMixin, TableObject):
    flag = 'i'
    flag_description = 'items and equipment'
    custom_random_enable = 'i'

    additional_bitnames = ['misc1', 'misc2']
    mutate_attributes = {
        'price': (1, 65500),
    }

    @property
    def name(self):
        return ItemNameObject.get(self.index).name_text.decode('utf8').strip()

    @property
    def is_coin_set(self):
        return 0x18a <= self.index <= 0x18d

    @property
    def is_coin_item(self):
        for s in ShopObject.every:
            if s.wares['coin'] and self.index in s.wares['item']:
                return True
        return False

    @property
    def is_new_coin_item(self):
        if hasattr(self, '_is_new_coin_item'):
            return self._is_new_coin_item
        self._is_new_coin_item = False
        return self.is_new_coin_item

    @property
    def is_unbuyable(self):
        for s in ShopObject.every:
            for key in s.wares:
                if self.index in s.wares[key]:
                    return False
        return True

    @property
    def is_blue_chest_item(self):
        return self in [b.item for b in BlueChestObject.every]

    @property
    def ip_shuffle_valid(self):
        if 'ip_effect' not in self.additional_properties:
            return False
        if self.index in [0x100, 0x105, 0x10a, 0x10e, 0x13f, 0x142]:
            return False
        return True

    @property
    def ip_shuffle_special(self):
        if not hasattr(self, 'extra'):
            self.read_extra()
        return self.extra[4:6] == '\x0c\x81'

    @property
    def alt_cursed(self):
        if self.get_bit('cursed'):
            return ItemObject.get(self.index+1)
        elif self.index == 0:
            return None
        else:
            test = ItemObject.get(self.index-1)
            if test.get_bit('cursed'):
                return test
        return None

    @property
    def rank(self):
        if hasattr(self, '_rank'):
            return self._rank

        price = self.old_data['price']

        rankdict = {
            0x00: -1,

            0x11: 20000,
            0x12: 20000,
            0x13: 20000,
            0x14: 20000,
            0x15: 20000,
            0x16: 20000,

            0x23: 1000,
            0x2c: 2000,
            0x2d: -1,

            0x2e: 20000,
            0x2f: 20000,
            0x30: 20000,
            0x31: 20000,
            0x32: 20000,
            0x33: 20000,
            0x34: 20000,
            0x35: 20000,

            0x1a6: 100 * 2000,

            0x1ce: 0,
            0x1cf: 0,
            0x1d1: 0,
            0x1d2: 0,
        }
        artemis_mods = ['L2_FRUE', 'L2_SPEKKIO', 'L2_KUREJI', 'L2_KUREJI_NB',
                        'L2_KUREJI_HC', 'L2_KUREJI_HC_NB']
        if get_global_label() in artemis_mods and self.index >= 0x1a7:
            self._rank = -1
        elif self.index in rankdict:
            self._rank = rankdict[self.index]
        elif 0x18e <= self.index <= 0x19b:
            self._rank = price * 2000
        elif price <= 2 or self.get_bit('unsellable'):
            self._rank = -1
        elif self.alt_cursed:
            self._rank = max(price, self.alt_cursed.price)
        else:
            self._rank = price
        self._rank = min(self._rank, 65000)
        return self.rank

    def cleanup(self):
        if self.index == 0x36 and 'KUREJI' in get_global_label().upper():
            for charname in ['maxim', 'selan', 'guy', 'artea',
                             'tia', 'dekar', 'lexis']:
                self.set_bit(charname, True)

        if self.is_new_coin_item and not self.is_coin_item:
            self.price = max(self.price, self.old_data['price'])
        if self.is_blue_chest_item or self.is_coin_item:
            self.set_bit('ban_ancient_cave', True)
        self.price = int(round(self.price))
        if self.is_coin_item:
            self.price = min(self.price, 2500)
            return
        if 's' not in get_flags() and 'i' not in get_flags():
            return
        self.price_clean()

    @staticmethod
    def intershuffle():
        ItemObject.class_reseed('ip')
        candidates = [i for i in ItemObject.ranked if i.ip_shuffle_valid]
        negranks = [c for c in candidates if c.rank < 0]
        for c in negranks:
            candidates.remove(c)
            assert c not in candidates
            max_index = len(candidates)
            index = random.randint(random.randint(random.randint(
                0, max_index), max_index), max_index)
            candidates.insert(index, c)

        cand2s = [c for c in candidates if c.ip_shuffle_special]
        cand1s = [c for c in candidates if c not in cand2s]
        for candidates in [cand1s, cand2s]:
            shuffled = shuffle_normal(
                candidates, wide=True, random_degree=ItemObject.random_degree)

            if candidates is cand2s:
                extras = [i.extra for i in shuffled]
                for i, extra in zip(candidates, extras):
                    startlen = len(i.extra)
                    i.extra = i.extra[:4] + extra[4:11] + i.extra[11:]
                    assert len(i.extra) == startlen

            shuffled = [i.additional_properties['ip_effect'] for i in shuffled]
            for i, ip in zip(candidates, shuffled):
                i.additional_properties['ip_effect'] = ip

        ItemObject.class_reseed('equip')
        equip_types = ['weapon', 'armor', 'shield',
                       'helmet', 'ring', 'jewel']
        for equip_type in equip_types:
            equips = [i for i in ItemObject.every
                      if i.get_bit('equipable') and i.get_bit(equip_type)]
            ordering = list(range(7))
            random.shuffle(ordering)
            for i in equips:
                old_equip = i.equipability
                assert not (old_equip & 0x80)
                new_equip = 0
                for n, m in enumerate(ordering):
                    if bool(old_equip & (1 << m)):
                        new_equip |= (1 << n)
                if random.random() < (ItemObject.random_degree ** 3):
                    new_equip = new_equip | (random.randint(0, 0x7f) &
                                             random.randint(0, 0x7f))
                if random.random() < (ItemObject.random_degree ** 1.5):
                    temp = new_equip & (random.randint(0, 0x7f) |
                                        random.randint(0, 0x7f))
                    if temp:
                        new_equip = temp
                assert new_equip
                i.equipability = new_equip

        equips = [i for i in ItemObject.every
                  if i.get_bit('equipable') and i.item_type & 0x3F]
        if 'everywhere' in get_activated_codes():
            # doesn't work, the game checks for multiple bits at equip menu
            print('EQUIP EVERYWHERE CODE ACTIVATED')
            for i in equips:
                equip_score = 6 - (bin(i.equipability).count('1') - 1)
                num_slots = 1 + ((equip_score / 6.0) * 5)
                assert equip_score >= 0
                num_slots = mutate_normal(
                    num_slots, minimum=1, maximum=6,
                    random_degree=ItemObject.random_degree ** 0.5, wide=True)
                bits = random.sample(range(6), num_slots)
                new_item_type = 0
                for b in bits:
                    new_item_type |= (1 << b)
                old_item_type = i.item_type
                i.item_type = 0
                for b in range(6):
                    if random.random() < ItemObject.random_degree:
                        i.item_type |= (new_item_type & (1 << b))
                    else:
                        i.item_type |= (old_item_type & (1 << b))
                assert not old_item_type & 0xC0

        elif 'anywhere' in get_activated_codes():
            # works, but 'strongest' looks for appropriate icon
            print('EQUIP ANYWHERE CODE ACTIVATED')
            for i in equips:
                if random.random() < (ItemObject.random_degree ** 1.5):
                    equip_type = random.choice(equip_types)
                    i.item_type = 0
                    i.set_bit(equip_type, True)

    @classmethod
    def mutate_all(cls):
        super(ItemObject, cls).mutate_all()
        addprops = ['increase_atp', 'increase_dfp', 'increase_str',
                    'increase_agl', 'increase_int', 'increase_gut',
                    'increase_mgr']
        minmaxes = {}
        for ap in addprops:
            candidates = [i for i in ItemObject.every
                          if ap in i.additional_properties]
            assert candidates
            values = [c.additional_properties[ap] for c in candidates]
            minmaxes[ap] = (min(values), max(values))

        for i in ItemObject.every:
            i.reseed(salt='mut2')
            for ap in addprops:
                if ap not in i.additional_properties:
                    continue
                lower, upper = minmaxes[ap]
                value = i.additional_properties[ap]
                value = mutate_normal(value, lower, upper,
                                      random_degree=ItemObject.random_degree)
                i.additional_properties[ap] = value


class ShopObject(TableObject):
    flag = 's'
    flag_description = 'shops'
    custom_random_enable = True

    def __repr__(self):
        s = 'SHOP %x\n' % self.index
        for menu in ['coin', 'item', 'weapon', 'armor']:
            if self.get_bit(menu):
                s += '%s\n' % menu.upper()
                for value in self.wares[menu]:
                    i = ItemObject.get(value)
                    s += '{0:12} {1}\n'.format(i.name, i.price)
        if self.get_bit('spell'):
            s += 'SPELL\n'
            for value in self.spells:
                s += '%s\n' % SpellObject.get(value).name
        return s.strip()

    @property
    def wares_flat(self):
        flat = []
        for menu in ['item', 'weapon', 'armor']:
            flat.extend(self.wares[menu])
        return [ItemObject.get(v) for v in flat]

    @classproperty
    def after_order(self):
        if 'i' in get_flags():
            return [ItemObject]
        else:
            ItemObject.ranked
        return []

    @classproperty
    def shop_items(self):
        items = set([])
        for s in ShopObject.every:
            for i in s.wares_flat:
                items.add(i)
        return sorted(items, key=lambda i: i.index)

    @classproperty
    def shop_spells(self):
        spells = set([])
        for s in ShopObject.every:
            spells |= set(s.spells)
        spells = [SpellObject.get(s) for s in spells]
        return sorted(spells, key=lambda s: s.index)

    @classproperty
    def shoppable_items(self):
        if hasattr(ShopObject, '_shoppable_items'):
            return ShopObject._shoppable_items

        assert hasattr(ItemObject.get(1), '_rank')
        shoppable_items = list(ShopObject.shop_items)
        for i in ItemObject.every:
            if (i not in shoppable_items and not i.get_bit('unsellable')
                    and i.rank == i.old_data['price'] and i.price > 0
                    and not i.is_coin_set):
                shoppable_items.append(i)
        shoppable_items = sorted(shoppable_items, key=lambda i: i.index)
        ShopObject._shoppable_items = shoppable_items
        return ShopObject.shoppable_items

    @classproperty
    def vanilla_buyable_items(self):
        return [ItemObject.get(i)
                for i in sorted(ShopObject.vanilla_buyable_indexes)]

    def read_data(self, filename=None, pointer=None):
        super(ShopObject, self).read_data(filename, pointer)
        filename = filename or self.filename

        if not hasattr(ShopObject, 'vanilla_buyable_indexes'):
            ShopObject.vanilla_buyable_indexes = set([])

        f = get_open_file(filename)
        f.seek(self.pointer+3)
        self.wares = {}
        for menu in ['coin', 'item', 'weapon', 'armor']:
            self.wares[menu] = []
            if self.get_bit(menu):
                assert not self.get_bit('pawn')
                assert not self.get_bit('spell')
                while True:
                    value = int.from_bytes(f.read(2), byteorder='little')
                    if value == 0:
                        break
                    self.wares[menu].append(value)
                    ShopObject.vanilla_buyable_indexes.add(value)

        self.spells = []
        if self.get_bit('spell'):
            assert self.shop_type == 0x20
            while True:
                value = ord(f.read(1))
                if value == 0xFF:
                    break
                self.spells.append(value)

    def write_data(self, filename=None, pointer=None):
        super(ShopObject, self).write_data(filename, pointer)
        filename = filename or self.filename

        f = get_open_file(filename)
        f.seek(self.pointer+3)
        for menu in ['coin', 'item', 'weapon', 'armor']:
            if self.get_bit(menu):
                assert self.wares[menu]
                assert not self.get_bit('pawn')
                assert not self.get_bit('spell')
                for value in self.wares[menu]:
                    f.write(value.to_bytes(length=2, byteorder='little'))
                f.write((0).to_bytes(length=2, byteorder='little'))

        if self.get_bit('spell'):
            assert self.shop_type == 0x20
            assert self.spells
            for value in self.spells:
                f.write(bytes([value]))
            f.write(b'\xff')

    @classmethod
    def full_randomize(cls):
        for cls2 in cls.after_order:
            if not (hasattr(cls2, 'randomized') and cls2.randomized):
                raise Exception('Randomize order violated: %s %s'
                                % (cls, cls2))

        ShopObject.class_reseed('full')
        shoppable_items = sorted(ShopObject.shoppable_items,
                                 key=lambda i: i.rank)
        coin_items = set([])
        for s in ShopObject.every:
            if s.wares['coin']:
                coin_items |= set(s.wares_flat)
        shuffled_items = shuffle_normal(
            shoppable_items, random_degree=ShopObject.random_degree)
        new_coin_items = set([])
        for a, b in zip(shoppable_items, shuffled_items):
            if a in coin_items:
                new_coin_items.add(b)
        for i in (coin_items - new_coin_items):
            i.price = min(i.price * 2000, 65000)
        for i in sorted(new_coin_items - coin_items, key=lambda i2: i2.index):
            # Dragonblade - 2500 -> 500000 coins
            if i in ShopObject.vanilla_buyable_items:
                i.price = max(i.price / 2000, 1)
            else:
                i.reseed(salt='coin')
                max_index = len(ItemObject.ranked)-1
                if i.rank < 0:
                    index = max_index
                else:
                    index = ItemObject.ranked.index(i)
                score = index / float(max_index)
                score = mutate_normal(score, 0, 1.0, wide=True,
                                      return_float=True,
                                      random_degree=ItemObject.random_degree)
                score = score ** (8 - (7*(ItemObject.random_degree ** 2)))
                assert 0 <= score <= 1
                price = int(round(score * 2500))
                price = min(2500, max(1, price))
                i.price = price
            i._is_new_coin_item = True

        non_coin_items = set(shoppable_items) - new_coin_items
        assert len(coin_items) == len(new_coin_items)

        for s in ShopObject.every:
            s.reseed(salt='mut')
            while True:
                badflag = False
                if s.wares_flat:
                    if s.wares['coin']:
                        candidates = new_coin_items
                    else:
                        candidates = non_coin_items
                    if ((s.wares['weapon'] or s.wares['armor'])
                            and not s.wares['coin']):
                        if not s.wares['weapon']:
                            candidates = [c for c in candidates
                                          if not c.get_bit('weapon')
                                          or not c.get_bit('equipable')]
                        if not s.wares['armor']:
                            candidates = [c for c in candidates
                                          if c.get_bit('weapon')
                                          or not c.get_bit('equipable')]
                        if not s.wares['item']:
                            candidates = [c for c in candidates
                                          if c.get_bit('equipable')]

                    new_wares = ItemObject.get_similar_set(
                        s.wares_flat, candidates)
                    d = {}
                    d['weapon'] = [i for i in new_wares if i.get_bit('weapon')]
                    d['armor'] = [i for i in new_wares
                                  if i.get_bit('equipable')
                                  and i not in d['weapon']]
                    d['item'] = [i for i in new_wares
                                 if i not in d['weapon'] + d['armor']]

                    if ((s.wares['weapon'] or s.wares['armor'])
                            and not s.wares['coin']):
                        for key in ['weapon', 'armor', 'item']:
                            a = len(s.wares[key])
                            b = len(d[key])
                            if bool(a) != bool(b):
                                badflag = True
                                break
                    else:
                        d['item'].extend(d['weapon'])
                        d['item'].extend(d['armor'])
                        d['weapon'] = []
                        d['armor'] = []

                    if badflag:
                        continue
                    for key in ['weapon', 'armor', 'item']:
                        if s.wares[key]:
                            s.wares[key] = sorted([i.index for i in d[key]])
                break

        spells = list(ShopObject.shop_spells)
        temp_spells = set([])
        shops = list(ShopObject.every)
        random.shuffle(shops)
        for p in shops:
            if not p.spells:
                continue
            if len(temp_spells) < len(p.spells):
                temp_spells = sorted(spells)
            old_spells = [SpellObject.get(s) for s in p.spells]
            new_spells = SpellObject.get_similar_set(old_spells, temp_spells)
            for n in new_spells:
                temp_spells.remove(n)
            p.spells = sorted([s.index for s in new_spells])

        for i in ShopObject.shop_items:
            if i.alt_cursed:
                i.price = max(i.price, i.alt_cursed.price)


class ItemNameObject(TableObject): pass


class MonsterMoveObject(TableObject):
    flag = 'm'

    def mutate(self):
        movements = [mm.old_data['movement']
                     for mm in MonsterMoveObject.every]
        movements.append(0x1F)
        movements_unique = sorted(set(movements))
        if random.random() <= get_random_degree():
            self.movement = random.choice(movements_unique)
        else:
            self.movement = random.choice(movements)

    def cleanup(self):
        if 'personnel' in get_activated_codes():
            self.movement = 0x1F


class MapMetaObject(TableObject):
    #FREE_SPACE = [(0x8a807, 0xa713d), (0x280000, 0x2a0000)]
    FREE_SPACE = [(0x280000, 0x2a0000)]

    class NPCPosition:
        def __init__(self, data):
            assert len(data) == 8
            self.index = data[0]
            self.x = data[1]
            self.y = data[2]
            self.boundary_west = data[3]
            self.boundary_north = data[4]
            self.boundary_east = data[5]
            self.boundary_south = data[6]
            self.misc = data[7]
            if {self.boundary_west, self.boundary_east,
                    self.boundary_north, self.boundary_south} != {0xff}:
                assert self.boundary_west < self.boundary_east
                assert self.boundary_north < self.boundary_south
                if self.x != 0xff:
                    assert self.boundary_west <= self.x < self.boundary_east
                if self.y != 0xff:
                    assert self.boundary_north <= self.y < self.boundary_south

        def __repr__(self):
            if self.is_mobile:
                s = ('X:{0:0>2x}<={1:0>2x}<={2:0>2x} '
                     'Y:{3:0>2x}<={4:0>2x}<={5:0>2x}')
                s = s.format(
                    self.boundary_west, self.x, self.boundary_east-1,
                    self.boundary_north, self.y, self.boundary_south-1)
            else:
                s = 'X:{0:0>2x} Y:{1:0>2x}'.format(self.x, self.y)
            return s

        @property
        def is_mobile(self):
            return (self.boundary_east - self.boundary_west > 1 or
                    self.boundary_south - self.boundary_north > 1)

        @property
        def bytecode(self):
            s = []
            for attr in ['index', 'x', 'y', 'boundary_west', 'boundary_north',
                         'boundary_east', 'boundary_south', 'misc']:
                value = getattr(self, attr)
                s.append(value)
            return bytes(s)

    @property
    def pretty_positions(self):
        self.set_event_signatures()
        s = ''
        for npcp in self.npc_positions:
            event_signature = '{0:0>2X}-C-{1:0>2X}'.format(
                self.index, npcp.index + 0x4f)
            s += '{0:0>2X} ({1:0>2X}) {2} [{3}]'.format(
                npcp.index, npcp.misc, npcp, event_signature)
            if npcp.extra_event_signature:
                s += ' [{0}]'.format(npcp.extra_event_signature)
            if npcp.sprite is not None:
                s += ' ROAMING {0}'.format(npcp.sprite)
            s += '\n'
        return s.strip()

    @property
    def roaming_npcs(self):
        return [exnpc for exnpc in RoamingNPCObject.every
                if exnpc.map_index == self.index]

    @property
    def npc_position_offset_length(self):
        data = self.old_data
        blocksize = len(data)
        offsets = []
        for i in range(1, 22):
            i *= 2
            offset = int.from_bytes(data[i:i+2], byteorder='little')
            offsets.append(offset)
        assert data[i+2] == 0xff
        offset_order = sorted(set(offsets) | {blocksize})

        npc_position_offset = offsets[7]
        assert npc_position_offset in offset_order
        index = offset_order.index(npc_position_offset)
        npc_position_length = offset_order[index+1] - npc_position_offset
        assert npc_position_length % 8 == 1
        return npc_position_offset, npc_position_length

    @property
    def bytecode(self):
        npcpo, npcpl = self.npc_position_offset_length
        assert npcpl >= 1
        header_data = self.old_data[:npcpo]
        footer_data = self.old_data[npcpo+npcpl:]
        old_npc_position_data = self.old_data[npcpo:npcpo+npcpl]

        npc_position_data = b''
        for npc_position in self.npc_positions:
            npc_position_data += npc_position.bytecode
        npc_position_data += b'\xff'
        new_npcpl = len(npc_position_data)
        npcpl_difference = new_npcpl - npcpl

        offsets = []
        for i in range(1, 22):
            i *= 2
            offset = int.from_bytes(header_data[i:i+2], byteorder='little')
            offsets.append(offset)

        assert offsets[7] == npcpo
        if len(self.npc_positions) > self.old_num_npcs:
            offsets[7] = len(self.old_data)
            footer_data += npc_position_data
            npc_position_data = old_npc_position_data
        else:
            while len(npc_position_data) < len(old_npc_position_data):
                npc_position_data += b'\xff'

        if self.npc_positions:
            assert offsets[7] > 0x2c
        else:
            assert offsets[7] == 0x2c
        assert all(o >= 0x2c for o in offsets)

        offset_str = b''.join([int.to_bytes(o, byteorder='little', length=2)
                               for o in offsets])
        blocksize = int.to_bytes(
            len(header_data + npc_position_data + footer_data),
            length=2, byteorder='little')
        header_data = (
            blocksize + offset_str + header_data[2+len(offset_str):])
        bytecode = header_data + npc_position_data + footer_data
        assert bytecode[0x2c] == 0xff
        return bytecode

    def set_event_signatures(self):
        for npcp in self.npc_positions:
            extra_matches = [exnpc for exnpc in self.roaming_npcs
                             if exnpc.map_npc_index == npcp.index]
            if extra_matches:
                assert len(extra_matches) == 1
                extra = extra_matches[0]
                sprite_index = extra.sprite_index
                map_npc_event_index = extra.map_npc_event_index
                event_signature = '{0:0>2X}-C-{1:0>2X}'.format(
                    self.index, map_npc_event_index)
                sprite = '{0:0>2x} {1}'.format(
                    extra.map_npc_event_index, names.sprites[sprite_index])
                npcp.extra_event_signature = event_signature
                npcp.sprite = sprite
            else:
                npcp.extra_event_signature = None
                npcp.sprite = None

    def get_npc_position_by_index(self, index):
        npcps = [npcp for npcp in self.npc_positions if npcp.index == index]
        if len(npcps) != 1:
            return None
        return npcps[0]

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)

        f = get_open_file(self.filename)
        pointer = map_from_lorom(self.reference_pointer)
        f.seek(pointer)
        blocksize = int.from_bytes(f.read(2), byteorder='little')
        f.seek(pointer)
        data = f.read(blocksize)
        self.old_data = data

        npcpo, npcpl = self.npc_position_offset_length
        npc_position_data = data[npcpo:npcpo+npcpl]

        assert npc_position_data[-1] == 0xff
        npc_position_data = npc_position_data[:-1]
        self.npc_positions = []
        while npc_position_data:
            npc_position = self.NPCPosition(npc_position_data[:8])
            npc_position_data = npc_position_data[8:]
            self.npc_positions.append(npc_position)
        self.old_num_npcs = len(self.npc_positions)
        assert self.old_data == self.bytecode

    def write_data(self, filename=None, pointer=None):
        blocksize = len(self.bytecode)
        candidates = sorted([(a, b) for (a, b) in MapMetaObject.FREE_SPACE
                             if b-a >= blocksize], key=lambda x: x[1]-x[0])
        lower, upper = candidates[0]
        MapMetaObject.FREE_SPACE.remove((lower, upper))
        assert lower+blocksize <= upper
        MapMetaObject.FREE_SPACE.append((lower+blocksize, upper))
        f = get_open_file(get_outfile())
        f.seek(lower)
        f.write(self.bytecode)
        self.reference_pointer = map_to_lorom(lower)
        super().write_data(filename, pointer)


class WordObject(TableObject):
    BASE_POINTER = 0x76a00

    @cached_property
    def word(self):
        word = b''
        f = get_open_file(self.filename)
        f.seek(self.BASE_POINTER + self.word_pointer)
        while True:
            c = f.read(1)
            if c == b'\x00':
                break
            word += c
        return word.decode('ascii')

    @clached_property
    def by_length(self):
        by_length = defaultdict(dict)
        for w in WordObject.every:
            if w.word[0] not in by_length[len(w.word)]:
                by_length[len(w.word)][w.word[0]] = []
            by_length[len(w.word)][w.word[0]].append(w)
        for k in by_length.keys():
            for c in by_length[k]:
                v = by_length[k][c]
                by_length[k][c] = sorted(v, key=lambda w: w.word)
        return by_length

    @classmethod
    def compress(self, message):
        oldmessage = message
        uncompressed = message
        uncompressed_raw = message
        target_length = len(uncompressed)
        for length in sorted(self.by_length.keys(), reverse=True):
            if length > target_length:
                continue
            head = uncompressed_raw[:(target_length-length)+1]
            candidate_chars = set(head)
            for c in sorted(candidate_chars):
                if c not in self.by_length[length]:
                    continue
                for w in self.by_length[length][c]:
                    if w.word in uncompressed:
                        if w.index >= 0x200:
                            replacement = '💙{0}💙'.format(
                                chr(0x80 | (w.index-0x200)))
                        elif w.index >= 0x100:
                            assert 0x100 <= w.index <= 0x1FF
                            replacement = '💙\x06{0}💙'.format(
                                chr(w.index-0x100))
                        else:
                            assert 0 <= w.index <= 0xFF
                            replacement = '💙\x05{0}💙'.format(chr(w.index))
                        message = message.replace(w.word, replacement)
                        uncompressed = uncompressed.replace(w.word, '💙')
                        uncompressed_raw = uncompressed.replace('💙', '')
                        target_length = len(uncompressed_raw)
                        if length > target_length:
                            break
        message = [m for m in message.split('💙') if m]
        return message


class RoamingNPCObject(TableObject):
    @property
    def sprite_name(self):
        return names.sprites[self.sprite_index]

class MapEventObject(TableObject):
    TEXT_PARAMETERS = {
        0x04: 1,
        0x05: 1,
        0x06: 1,
        0x0a: 2,
        }
    TEXT_TERMINATORS = {0x00, 0x01, 0x0b}

    ASCII_VISIBLE = ascii_letters + digits + punctuation + ' '
    CHARACTER_MAP = {
        0x00: '<END EVENT>',
        0x01: '<END MESSAGE>',
        0x03: '\n',
        0x04: '<PAUSE>',
        0x09: '$MAXIM$',
        0x0a: '<REPEAT>',
        0x0b: '<CHOICE>',
        0x0c: '?\n',
        0x0d: '!\n',
        0x0e: ',\n',
        0x0f: '.\n',
        }
    REVERSE_CHARACTER_MAP = {v: k for k, v in CHARACTER_MAP.items()}
    TAG_MATCHER = re.compile('<([^>]*) ([^> ]*)>')

    END_NPC_POINTER = 0x3ae4d
    END_EVENT_POINTER = 0x7289e
    FREE_SPACE = [(0x3aed8, 0x3af4c)]

    roaming_comments = set()

    class EventList:
        def __init__(self, pointer, meo):
            self.pointer = pointer
            self.meo = meo
            if self.pointer == self.meo.npc_pointer:
                self.script_pointers = [(None, self.pointer)]
                return

            f = get_open_file(get_outfile())
            f.seek(pointer)
            self.script_pointers = []
            while True:
                index = ord(f.read(1))
                if index == 0xFF:
                    break
                script_pointer = int.from_bytes(f.read(2), byteorder='little')
                self.script_pointers.append(
                    (index, self.meo.eventlists_pointer + script_pointer))
            MapEventObject.deallocate((self.pointer, f.tell()))

        def __repr__(self):
            s = ''
            for script in self.scripts:
                s += '\n' + script.pretty_with_header + '\n'
            return s.strip()

        @cached_property
        def index(self):
            i = self.meo.event_lists.index(self)
            return 'XABCDEF'[i]

        @property
        def map_meta(self):
            return self.meo.map_meta

        @property
        def eventlists_pointer(self):
            return self.meo.eventlists_pointer

        @property
        def size_estimate(self):
            if self.index == 'X':
                return len(self.script.data)
            total = (len(self.scripts)*3) + 1
            for script in self.scripts:
                total += len(script.data)
            return total

        def get_script_by_index(self, index):
            if self.index == 'X':
                assert index is None
                assert len(self.scripts) == 1
                return self.scripts[0]

            candidates = [s for s in self.scripts if s.index == index]
            assert len(candidates) == 1
            return candidates[0]

        def read_scripts(self):
            self.scripts = []
            for index, p1 in sorted(self.script_pointers):
                p2 = min(p for p in MapEventObject.ALL_POINTERS if p > p1)
                script = MapEventObject.Script(p1, p2-p1, self, index=index)
                script.deallocate()
                self.scripts.append(script)
            if DEBUG_MODE:
                for script in self.scripts:
                    if script.frozen:
                        continue
                    script.data = script.compile()
                    script.script = script.parse()
                    script.import_script(script.pretty)
                    assert script.validate_no_change()
                    script.script = script.old_script

        def write(self):
            for script in self.scripts:
                assert script.event_list is self
            f = get_open_file(get_outfile())

            npc_loader = (self.index == 'X')
            if npc_loader:
                assert len(self.scripts) == 1
                script = self.scripts[0]
                data = script.compile(optimize=True)
                assert data[-1] == 0
                self.pointer = MapEventObject.allocate(
                    len(data), npc_loader=npc_loader)
                script.script_pointer = self.pointer
                script.data = script.compile(optimize=True)
                f.seek(script.script_pointer)
                f.write(script.data)
                assert f.tell() == self.pointer + len(data)
                return

            self.pointer = MapEventObject.allocate(
                (len(self.scripts)*3) + 1, near=self.meo.eventlists_pointer)
            f.seek(self.pointer)
            for i, script in enumerate(self.scripts):
                if script.index == 0 and not hasattr(self.meo,
                                                     'assigned_zero'):
                    self.meo.assigned_zero = self.pointer + (i*3)

                data = script.compile(optimize=True, ignore_pointers=True)
                assert data[-1] == 0
                if data[0] == 0:
                    assert hasattr(self.meo, 'assigned_zero')
                    if (DEBUG_MODE and
                            self.meo.assigned_zero != self.pointer + (i*3)):
                        f.flush()
                        f.seek(self.meo.assigned_zero)
                        peek = f.read(1)
                        assert peek == b'\x00'
                    script.script_pointer = self.meo.assigned_zero
                else:
                    script.script_pointer = MapEventObject.allocate(
                        len(data), npc_loader=npc_loader,
                        find_best_fit_dry=True,
                        near=[self.meo.eventlists_pointer, self.pointer],
                        )
                    assert 0 <= script.script_pointer - self.meo.eventlists_pointer <= 0xffff
                    assert 0 <= script.script_pointer - self.pointer <= 0xffff
                    script.data = script.compile(optimize=True)
                    #assert len(script.data) == len(data)
                    MapEventObject.allocate(
                        len(script.data), npc_loader=npc_loader,
                        forced=script.script_pointer)
                    f.seek(script.script_pointer)
                    f.write(script.data)
                script_pointer = script.script_pointer
                offset = script_pointer - self.meo.eventlists_pointer
                assert 0 <= offset <= 0xffff
                f.seek(self.pointer + (3*i))
                f.write(bytes([script.index]))
                f.write(offset.to_bytes(2, byteorder='little'))
            f.write(b'\xff')
            assert f.tell() == self.pointer + (3 * len(self.scripts)) + 1

    class Script:
        INSTRUCTIONS_FILENAME = path.join(tblpath, 'event_instructions.txt')
        FULL_PARAMETERS = {}
        COMMENTS = {}
        for line in read_lines_nocomment(INSTRUCTIONS_FILENAME):
            while '  ' in line:
                line = line.replace('  ', ' ')
            line = line.split(' ', 2)
            if len(line) == 2:
                opcode, num_parameters = line
                comment = None
            else:
                opcode, num_parameters, comment = line
            opcode = int(opcode, 0x10)
            temp = num_parameters.split(',')
            temp = [int(p) if p in digits else p for p in temp]
            temp = [p for p in temp if p != 0]
            FULL_PARAMETERS[opcode] = temp
            if comment:
                COMMENTS[opcode] = comment

        ADDRESS_MATCHER = re.compile('@([0-9A-Fa-f]+)[^0-9A-Fa-f]',
                                     flags=re.DOTALL)

        class Address:
            def __init__(self, address, is_local):
                assert 0 <= address <= 0x7fff
                self.address = address
                self.old_address = address
                self.is_local = is_local
                if not is_local:
                    raise NotImplementedError('Non-local address.')

            def __repr__(self):
                return '{0}{1:X}'.format('@' if self.is_local else '&',
                                         self.address)

            def __copy__(self):
                return self(self.address, self.is_local)

        def __init__(self, script_pointer, data_length,
                     event_list=None, index=None):
            self.script_pointer = script_pointer
            self.event_list = event_list
            self.index = index
            self.frozen = False

            f = get_open_file(get_outfile())
            f.seek(self.script_pointer)
            self.data = f.read(data_length)

            self.old_script_pointer = self.script_pointer
            self.old_base_pointer = self.base_pointer
            self.old_data = self.data

            self.script = self.parse()
            self.old_script = deepcopy(self.script)
            self.old_pretty = self.pretty

        def __repr__(self):
            return self.pretty_with_header

        @property
        def eventlists_pointer(self):
            return self.event_list.eventlists_pointer

        @property
        def map_meta(self):
            return self.event_list.map_meta

        @property
        def is_npc_load_event(self):
            return self.script_pointer < MapEventObject.MIN_EVENT_LIST

        @property
        def base_pointer(self):
            if not self.is_npc_load_event:
                return self.eventlists_pointer
            else:
                return self.script_pointer & 0xff8000

        @property
        def pretty(self):
            pretty = self.prettify_script(self.script)
            address_matches = self.ADDRESS_MATCHER.findall(pretty)
            done_labels = set()
            for match in address_matches:
                offset = int(match, 0x10)
                if offset in done_labels:
                    continue
                done_labels.add(offset)
                linecode = '{0:0>4X}. '.format(offset)
                index = pretty.index(linecode)
                replacement = '# LABEL @{0:X} ${1:x}\n{2}'.format(
                    offset, self.script_pointer+offset, linecode)
                pretty = pretty.replace(linecode, replacement)
            return pretty.rstrip()

        @property
        def header(self):
            header = 'EVENT {0}  # ${1:x}:{2:x}'.format(
                self.signature, self.event_list.pointer, self.script_pointer)
            return header

        @property
        def signature(self):
            if self.index is not None:
                si = '{0:0>2X}'.format(self.index)
            else:
                si = 'XX'
            return '{0:0>2X}-{1}-{2}'.format(
                self.event_list.meo.index, self.event_list.index, si)

        @property
        def pretty_with_header(self):
            s = '{0}\n{1}'.format(self.header, self.pretty)
            s = s.replace('\n', '\n  ')
            return s.strip()

        @property
        def opcount(self):
            return Counter(
                [opcode for line_number, opcode, parameters in self.script])

        @cached_property
        def pre_data(self):
            pointer = self.script_pointer - 0x1000
            assert pointer >= 0
            f = get_open_file(get_outfile())
            f.seek(pointer)
            return f.read(0x1000)

        @classmethod
        def get_pretty_variable(self, variable):
            vname = 'Variable {0:0>2X} (${1:0>4x})'.format(
                variable, variable + 0x079e)
            return vname

        @classmethod
        def get_pretty_flag(self, flag):
            address = 0x77e + (flag // 8)
            bit = 1 << (flag % 8)
            fname = 'Flag {0:0>2X} (${1:0>4x}:{2:0>2x})'.format(
                flag, address, bit)
            return fname

        def prettify_script(self, script):
            pretty = ''
            for line_number, opcode, parameters in script:
                line = ''
                if self.FULL_PARAMETERS[opcode] == ['text']:
                    text = MapEventObject.prettify_text(parameters)
                    textlines = text.split('\n')
                    justifiers = ['{0:0>2X}:'.format(opcode)]
                    justifiers += ([''] * len(textlines))
                    for left, right in zip(justifiers, textlines):
                        line += '{0:3} {1}\n'.format(left, right)
                    line = line.rstrip()
                    line = line.replace('\n', '\n      ')
                    line = '{0:0>4X}. {1}'.format(line_number, line)
                else:
                    if len(parameters) > 16:
                        paramstr = hexify(parameters[:16])
                        paramstr += '... [{0} bytes]'.format(len(parameters))
                    else:
                        params = []
                        parameter_types = list(
                            self.FULL_PARAMETERS[opcode])
                        if ('variable' in parameter_types
                                and parameters[0] in {0xc0, 0xc2}):
                            assert len(parameter_types) == 1
                            parameter_types += [2, 2]
                        while len(parameter_types) < len(parameters):
                            if isinstance(parameter_types[-1], int):
                                assert 'variable' in parameter_types
                                parameter_types.append(1)
                            else:
                                parameter_types.append(parameter_types[-1])

                        for pt, p in zip(parameter_types, parameters):
                            if isinstance(p, int):
                                if pt in ['pointers', 'variable']:
                                    pt = 1
                                assert isinstance(pt, int)
                                assert pt > 0
                                s = ('{0:0>%sX}' % (pt * 2)).format(p)
                            else:
                                assert isinstance(p, self.Address)
                                s = str(p)
                            params.append(s)
                        paramstr = '-'.join(params)
                    line = '{0:0>2X}({1})'.format(opcode, paramstr)

                    # determine custom comments
                    if opcode in self.COMMENTS:
                        comment = self.COMMENTS[opcode]
                    else:
                        comment = ''

                    if opcode in [0x68, 0x7b]:
                        npc_index, sprite_index = parameters
                        if self.map_meta:
                            position = self.map_meta.get_npc_position_by_index(
                                npc_index-0x4f)
                        else:
                            position = None
                        name = names.sprites[sprite_index]
                        if position:
                            x, y = position.x, position.y
                            x = '{0:0>2x}'.format(x)
                            y = '{0:0>2x}'.format(y)
                        else:
                            x, y = '??', '??'
                        comment += ' ({0},{1}) {2:0>2x}: {3:0>2x} {4}'.format(
                            x, y, npc_index, sprite_index, name)
                        comment += '\n'
                    elif opcode == 0x53:
                        (formation_index,) = parameters
                        f = FormationObject.get(formation_index)
                        comment = '{0} ({1})'.format(comment, f.name)
                    elif opcode in {0x20, 0x21}:
                        item_index, quantity = parameters
                        item_index |= (0x100 * (opcode-0x20))
                        item = ItemObject.get(item_index)
                        comment = '{0} ({1} x{2})'.format(
                            comment, item.name, quantity)
                    elif opcode == 0x23:
                        character_index, spell_index = parameters
                        character = CharacterObject.get(character_index)
                        spell = SpellObject.get(spell_index)
                        comment = '{0} ({1}: {2})'.format(
                            comment, character.name, spell.name)
                    elif opcode == 0x16:
                        event = '{0:0>2X}-B-{1:0>2X} ({2:0>2X})'.format(
                            *parameters)
                        comment = '{0} {1}'.format(comment, event)
                    elif opcode == 0x35:
                        assert parameters[0] >= 0x10
                        xnpc = RoamingNPCObject.get(parameters[0] - 0x10)
                        npc_signature = '({0:0>2X} {1})'.format(
                            parameters[0], xnpc.sprite_name)
                        loc_signature = '(map {0:0>2X}, NPC {1:0>2X})'.format(
                            parameters[1], parameters[2])
                        comment = 'Move roaming NPC {0} to {1}'.format(
                            npc_signature, loc_signature)
                        comment += ' [{0:0>2X}-C-{1:0>2X}]'.format(
                            parameters[1], parameters[0])
                        roaming_comment = '[{0}] {1}'.format(
                            self.signature, comment)
                        MapEventObject.roaming_comments.add(roaming_comment)
                    elif opcode == 0x14:
                        assert parameters[-3] in {0x20, 0x30}
                        assert isinstance(parameters[-2], self.Address)
                        assert parameters[-1] == 0xFF
                        conditions = parameters[:-3]
                        s = 'If'
                        while conditions:
                            c = conditions.pop(0)
                            if c == 0xf0:
                                s += ' NPC ???'
                                conditions.pop(0)
                                conditions.pop(0)
                            elif c == 0xf8:
                                npc_index = conditions.pop(0)
                                assert npc_index >= 1
                                s += ' NPC {0:0>2X} ???'.format(npc_index-1)
                                conditions.pop(0)
                            elif c in {0xc0, 0xc2}:
                                item_index = conditions.pop(0)
                                item_name = ItemObject.get(item_index).name
                                quantity = conditions.pop(0)
                                if c == 0xc0:
                                    s += ' exactly {0} x{1} owned'.format(
                                        item_name, quantity)
                                elif c == 0xc2:
                                    s += ' at least {0} x{1} owned'.format(
                                        item_name, quantity)
                            elif c in {0x10, 0x12}:
                                variable = conditions.pop(0)
                                value = conditions.pop(0)
                                vname = self.get_pretty_variable(variable)
                                if c == 0x10:
                                    s += ' {0} == {1}'.format(vname, value)
                                elif c == 0x12:
                                    s += ' {0} >= {1}'.format(vname, value)
                            else:
                                assert c in {0x00, 0x40, 0x80,
                                             0x01, 0x41, 0x81}
                                if c & 0x40:
                                    s += ' OR'
                                elif c & 0x80:
                                    s += ' AND'
                                flag = conditions.pop(0)
                                s += ' ' + self.get_pretty_flag(flag)
                                if c & 1:
                                    s += ' NOT'
                                s += ' set'
                        if parameters[-3] == 0x30:
                            s += " then DON'T jump to {0}".format(
                                parameters[-2])
                        elif parameters[-3] == 0x20:
                            s += " then jump to {0}".format(parameters[-2])
                        comment = s.strip()
                        assert '  ' not in comment

                    if comment.endswith('Flag'):
                        flag = parameters[0]
                        comment = comment.replace(
                            'Flag', self.get_pretty_flag(flag))

                    if comment.endswith('Variable'):
                        variable = parameters[0]
                        comment = comment.replace(
                            'Variable', self.get_pretty_variable(variable))

                    if comment.strip():
                        line = '{0:0>4X}. {1:30} # {2}'.format(line_number,
                                                               line, comment)
                    else:
                        line = '{0:0>4X}. {1}'.format(line_number, line)
                pretty += line.rstrip() + '\n'
            return pretty.rstrip()

        def make_pointer(self, data):
            assert len(data) == 2
            offset = int.from_bytes(data, byteorder='little')
            pointer = self.base_pointer + offset
            is_local_pointer = (self.script_pointer <= pointer
                                < self.script_pointer + len(self.data))
            if is_local_pointer:
                script_offset = self.script_pointer - self.base_pointer
                return self.Address(offset-script_offset,
                                    is_local_pointer)
            else:
                return self.Address(pointer, is_local_pointer)

        def parse_text(self, opcode, data, full_data=None):
            if full_data is None:
                full_data = self.data

            text = []
            if opcode == 0x13:
                npc_index, data = data[:1], data[1:]
                text.append(('NPC', npc_index))
            elif opcode in {0x6d, 0x6e}:
                position, data = data[:2], data[2:]
                text.append(('POSITION', position))
            elif opcode == 0x9e:
                unknown, data = data[:1], data[1:]
                text.append(('UNKNOWN', unknown))
            text.append((None, b''))

            while True:
                try:
                    textcode, data = data[0], data[1:]
                except IndexError:
                    break

                if textcode in MapEventObject.TEXT_TERMINATORS:
                    text.append((textcode, b''))
                    break
                elif textcode == 0xa:
                    n = MapEventObject.TEXT_PARAMETERS[textcode]
                    text_parameters, data = data[:n], data[n:]
                    value = int.from_bytes(text_parameters, byteorder='little')
                    length = (value >> 12) + 2
                    pointer = (value & 0xfff) + 2
                    consumed_data = full_data[:-len(data)]
                    buffer_data = self.pre_data + consumed_data
                    index = len(buffer_data) - pointer
                    assert index >= 0
                    repeat_text = buffer_data[index:index+length]
                    assert len(repeat_text) == length
                    text.append((None, repeat_text))

                elif textcode in MapEventObject.TEXT_PARAMETERS:
                    n = MapEventObject.TEXT_PARAMETERS[textcode]
                    text_parameters, data = data[:n], data[n:]
                    assert len(text_parameters) == n
                    text.append((textcode, text_parameters))
                else:
                    if text[-1][0] is not None:
                        text.append((None, b''))
                    a, b = text.pop()
                    assert a is None
                    b += bytes([textcode])
                    text.append((a, b))

            text = [(a, b) for (a, b) in text if b or (a is not None)]
            for a, b in zip(text, text[1:]):
                if a is None:
                    assert b is not None

            return text, data

        @classmethod
        def trim_script(self, script):
            for i in range(len(script)-1, -1, -1):
                _, opcode, parameters = script[i]
                if opcode == 0:
                    assert not parameters
                    script = script[:i+1]
                    break
                elif 'text' in self.FULL_PARAMETERS[opcode]:
                    #self.CHARACTER_MAP[parameters[-1][-1]] == '<END EVENT>'
                    charcode = parameters[-1][0]
                    if MapEventObject.CHARACTER_MAP[charcode] == '<END EVENT>':
                        break
            else:
                raise AssertionError('Script does not terminate.')
            return script

        def parse(self, data=None):
            if self.frozen:
                return self.old_script
            if data is None:
                data = self.data
            full_data = data
            script = []
            try:
                while data:
                    consumed = len(full_data) - len(data)
                    opcode, data = data[0], data[1:]
                    assert opcode in self.FULL_PARAMETERS
                    parameter_types = self.FULL_PARAMETERS[opcode]
                    parameters = []
                    for pt in parameter_types:
                        assert pt != 0
                        if pt == 'text':
                            repeat_pointer = self.script_pointer + consumed + 1
                            text, data = self.parse_text(opcode, data)
                            parameters.extend(text)
                        elif pt == 'pointers':
                            num_pointers, data = data[0], data[1:]
                            parameters.append(num_pointers)
                            for i in range(num_pointers):
                                pointer = self.make_pointer(data[:2])
                                data = data[2:]
                                parameters.append(pointer)
                        elif pt == 'variable':
                            assert opcode == 0x14
                            while True:
                                c, data = data[0], data[1:]
                                parameters.append(c)
                                if c == 0xff:
                                    break
                                elif c & 0xf0 == 0xf0:
                                    assert len(parameters) == 1
                                    assert c in {0xf0, 0xf8}
                                    # 0xf0 Monster on button
                                    # 0xf8 if NPC state
                                    parameters.append(data[0])
                                    parameters.append(data[1])
                                    data = data[2:]
                                elif c & 0xf0 == 0xc0:
                                    # ???
                                    assert len(parameters) == 1
                                    assert c in {0xc0, 0xc2}
                                    # 0xc0 Check item possessed exactly number
                                    # 0xc2 Check item possessed GTE
                                    item_index, data = data[:2], data[2:]
                                    item_number, data = data[:2], data[2:]
                                    item_index = int.from_bytes(
                                        item_index, byteorder='little')
                                    item_number = int.from_bytes(
                                        item_number, byteorder='little')
                                    parameters.append(item_index)
                                    parameters.append(item_number)
                                elif c & 0xf0 == 0x10:
                                    assert len(parameters) == 1
                                    assert c in {0x10, 0x12}
                                    # 0x10 Equals
                                    # 0x12 GTE
                                    parameters.append(data[0])
                                    parameters.append(data[1])
                                    data = data[2:]
                                elif c & 0xe0 == 0x20:
                                    assert c in {0x20, 0x30}
                                    # 0x20 Branch if True
                                    # 0x30 Branch if False
                                    pointer = self.make_pointer(data[:2])
                                    data = data[2:]
                                    parameters.append(pointer)
                                else:
                                    assert c in {0x00, 0x01,
                                                 0x40, 0x41,
                                                 0x80, 0x81}
                                    # 0x01 NOT
                                    # 0x40 OR
                                    # 0x80 AND
                                    flag, data = data[0], data[1:]
                                    parameters.append(flag)
                        elif pt == 'addr':
                            pointer = self.make_pointer(data[:2])
                            data = data[2:]
                            parameters.append(pointer)
                        else:
                            assert isinstance(pt, int)
                            assert pt > 0
                            assert len(data) >= pt
                            parameter, data = data[:pt], data[pt:]
                            parameter = int.from_bytes(parameter,
                                                       byteorder='little')
                            parameters.append(parameter)
                    if not script:
                        assert consumed == 0
                    else:
                        assert consumed > 0
                    script.append((consumed, opcode, parameters))
                    if script == [(0, 0, [])]:
                        break
            except AssertionError:
                print('WARNING: Script {0:x}.'.format(self.script_pointer))
                try:
                    script = self.trim_script(script)
                except AssertionError:
                    print('WARNING: Script {0:x} does not terminate.'.format(
                        self.script_pointer))
                    script.append((len(full_data), 0, []))
            return script

        def import_script(self, template, **kwargs):
            assert not self.frozen
            if hasattr(self, '_imported') and self._imported:
                print('WARNING: Script {0:x} double imported.'.format(
                    self.script_pointer))
            self._imported = True
            text = template
            for key, value in sorted(kwargs.items()):
                to_replace = '{%s}' % key
                if isinstance(value, int):
                    value = '{0:X}'.format(value)
                text = text.replace(to_replace, value)

            line_matcher = re.compile('^ *([0-9A-Fa-f]+)\. (.*)$')
            lines = []
            prevno, prevline = None, None
            seen_line_numbers = set()
            for line in text.split('\n'):
                if '#' in line:
                    line = line.split('#')[0]
                line = line.rstrip()
                if not line:
                    continue
                match = line_matcher.match(line)
                if lines:
                    prevno, prevline = lines[-1]
                if match:
                    line_number = int(match.group(1), 0x10)
                    if prevno is not None and prevno >= line_number:
                        raise Exception(
                            'SCRIPT {0:x} ERROR: Lines out of order.'.format(
                                self.script_pointer))
                    lines.append((line_number, match.group(2)))
                    seen_line_numbers.add(line_number)
                else:
                    lines[-1] = (prevno, '\n'.join([prevline, line.strip()]))

            script = []
            try:
                for line_number, line in lines:
                    assert line[2] in '(:'
                    opcode = int(line[:2], 0x10)
                    if line[2] == '(':
                        assert line[-1] == ')'
                        parameters = line[3:-1]
                        assert '(' not in parameters and ')' not in parameters
                        if parameters:
                            parameters = parameters.split('-')
                        else:
                            parameters = []
                        params = []
                        for p in parameters:
                            if p.startswith('@'):
                                offset = int(p[1:], 0x10)
                                is_local = offset in seen_line_numbers
                                assert is_local
                                addr = self.Address(address=offset,
                                                    is_local=is_local)
                                params.append(addr)
                            else:
                                params.append(int(p, 0x10))
                        script.append((line_number, opcode, params))
                    elif line[2] == ':':
                        linetext = line[3:].strip()
                        compress = opcode not in {0x6d, 0x6e}
                        newtext = MapEventObject.reverse_prettify_text(
                            linetext, compress=compress)
                        newscript = self.parse(bytes([opcode]) + newtext)
                        newpretty = self.prettify_script(newscript)
                        for linetextline in linetext.split('\n'):
                            assert linetextline in newpretty
                        assert len(newscript) == 1
                        new_number, new_op, new_params = newscript[0]
                        assert new_op == opcode
                        script.append((line_number, opcode, new_params))
            except:
                raise Exception(
                    'SCRIPT {0:x} ERROR: {1}. {2}'.format(
                        self.script_pointer, line_number, line))

            self.script = script
            return script

        def compress(self, text, compress=True):
            assert isinstance(text, bytes)
            old_buffer_length = len(self.compression_buffer)
            while text:
                maxlength = min(17, len(self.compression_buffer), len(text))
                for length in range(maxlength, 3, -1):
                    if not compress:
                        continue
                    substr = ''.join(chr(c) for c in text[:length])
                    if any([ord(c) & 0x80 for c in substr]):
                        continue
                    if substr not in self.compression_buffer:
                        continue
                    subdata = self.compression_buffer[-0xffe:]
                    subdata += '\x0a'
                    if substr not in subdata:
                        continue
                    pointer = len(subdata) - subdata.index(substr)
                    length_field = (length - 2) << 12
                    assert pointer <= 0xfff
                    assert length_field & pointer == 0
                    fields = length_field | pointer
                    assert fields <= 0xffff
                    # Compression is better? Need to test.
                    self.compression_buffer += '\x0a'
                    self.compression_buffer += chr(fields & 0xff)
                    self.compression_buffer += chr(fields >> 8)
                    text = text[length:]
                    break
                else:
                    self.compression_buffer += chr(ord(text[:1]))
                    text = text[1:]
            return_length = len(self.compression_buffer) - old_buffer_length
            return_text = self.compression_buffer[-return_length:]
            assert len(return_text) == return_length
            return return_text

        def realign_addresses(self):
            # TODO: Unused method?
            line_numbers = [ln for (ln, _, _) in self.script]
            new_script = []
            for i, (line_number, opcode, parameters) in enumerate(self.script):
                try:
                    next_line_number = self.script[i+1][0]
                except IndexError:
                    next_line_number = None
                addrs = [p for p in parameters if isinstance(p, self.Address)]
                for p in addrs:
                    addr = p.address
                    if addr not in line_numbers:
                        addr = min([ln for ln in line_numbers
                                    if ln >= addr])
                        p.address = addr
                if len(addrs) == 1:
                    addr = addrs[0]
                    if addr.address == next_line_number:
                        continue
                new_script.append((line_number, opcode, parameters))
            self.script = new_script

        def compile(self, script=None, optimize=False, ignore_pointers=False):
            if self.frozen:
                return self.old_data
            if script is None:
                script = self.script
            partial = {}
            previous_line_number = None
            self.compression_buffer = ''
            prevop = None
            assigned_zero = None
            zero_lines = set()
            for line_number, opcode, parameters in script:
                if opcode == 0:
                    zero_lines.add(line_number)
                    if assigned_zero is None:
                        assigned_zero = line_number
                    elif prevop == 0 and optimize:
                        continue
                prevop = opcode
                if isinstance(line_number, str):
                    line_number = int(line_number, 0x10)
                if previous_line_number is not None:
                    assert line_number > previous_line_number
                previous_line_number = line_number

                parameter_types = list(self.FULL_PARAMETERS[opcode])
                if ('variable' in parameter_types
                        and parameters[0] in {0xc0, 0xc2}):
                    assert len(parameter_types) == 1
                    parameter_types += [2, 2]
                while len(parameter_types) < len(parameters):
                    if isinstance(parameter_types[-1], int):
                        assert 'variable' in parameter_types
                        parameter_types.append(1)
                    else:
                        parameter_types.append(parameter_types[-1])
                assert len(parameter_types) == len(parameters)

                line = []
                def append_data(to_append):
                    if not isinstance(to_append, list):
                        to_append = [to_append]
                    for ta in to_append:
                        if isinstance(ta, self.Address):
                            line.append(ta)
                            line.append(None)
                            self.compression_buffer += '💙💙'
                        elif isinstance(ta, int):
                            line.append(ta)
                            self.compression_buffer += chr(ta)
                        else:
                            raise Exception('Unexpected data type.')

                append_data(opcode)
                for pt, parameter in zip(parameter_types, parameters):
                    if pt == 'text':
                        label, value = parameter
                        if isinstance(label, int):
                            append_data(label)
                            if value:
                                assert len(value) == 1
                                value = ord(value)
                                assert 0 <= value <= 0xff
                                append_data(value)
                        elif label is None:
                            assert isinstance(value, bytes)
                            compress = opcode not in {0x6d, 0x6e}
                            value = self.compress(value, compress=compress)
                            line += [ord(c) for c in value]
                        elif isinstance(value, bytes):
                            append_data([c for c in value])
                        else:
                            assert False
                            assert isinstance(value, int)
                            assert 0 <= value <= 0xFF
                            append_data(value)
                        continue

                    if isinstance(parameter, self.Address):
                        append_data(parameter)
                    elif pt in ['pointers', 'variable']:
                        append_data(parameter)
                    else:
                        assert isinstance(pt, int)
                        value = parameter.to_bytes(pt, byteorder='little')
                        append_data([v for v in value])

                partial[line_number] = line

            address_conversions = {}
            running_length = 0
            for line_number in sorted(partial):
                assert running_length >= 0
                address_conversions[line_number] = running_length
                running_length += len(partial[line_number])

            new_data = b''
            for line_number, line in sorted(partial.items()):
                for value in line:
                    if isinstance(value, self.Address) and not ignore_pointers:
                        assert value.is_local
                        if optimize and value.address in zero_lines:
                            value.address = assigned_zero
                        value.address = address_conversions[value.address]

                new_line = []
                for value in line:
                    if value is None:
                        continue
                    elif isinstance(value, self.Address):
                        script_offset = self.script_pointer - self.base_pointer
                        address = value.address + script_offset
                        if ignore_pointers:
                            address = 0
                        assert 0 <= address <= 0xffff
                        new_line.append(address & 0xFF)
                        new_line.append(address >> 8)
                    else:
                        new_line.append(value)

                new_data += bytes(new_line)

            if not ignore_pointers:
                self.data = new_data
                self.script = self.parse(new_data)
            return new_data

        def validate_no_change(self):
            old = self.old_pretty
            new = self.pretty
            while '  ' in old:
                old = old.replace('  ', ' ')
            while '  ' in new:
                new = new.replace('  ', ' ')
            old = re.sub('\n..... ', '\n', old)
            new = re.sub('\n..... ', '\n', new)
            old = re.sub('@[^-)]+', '', old)
            new = re.sub('@[^-)]+', '', new)
            if DEBUG_MODE and old != new:
                olds = old.split('\n')
                news = new.split('\n')
                for a, b in zip(olds, news):
                    if a != b:
                        print()
                        print(a)
                        print(b)
                        import pdb; pdb.set_trace()
                    else:
                        print(a)
            return old == new

        def deallocate(self):
            assert self.data == self.old_data
            MapEventObject.deallocate((self.script_pointer,
                                       self.script_pointer + len(self.data)))

    # MapEventObject methods
    def __repr__(self):
        s1 = '# MAP {0:0>2X}-{1:0>5x} ({2})\n'.format(
            self.index, self.pointer, self.name)
        check = '[{0:0>2X}'.format(self.index)
        roamings = [c for c in self.roaming_comments if check in c]
        outroamings = [c for c in roamings if c.startswith(check)]
        inroamings = [c for c in roamings if c not in outroamings]
        s2, s3 = '', ''
        for c in sorted(inroamings):
            s1 += '# ' + c + '\n'
        for c in sorted(outroamings):
            s3 += '# ' + c + '\n'
        if self.map_meta.npc_positions:
            s2 += '\n' + self.map_meta.pretty_positions
            s2 = s2.replace('\n', '\n# NPC ') + '\n'
        assert self.event_lists[0].index == 'X'
        npc_preload_matcher = re.compile(
            '.*([0-9a-fA-F]{2}): (.*)$')
        preload_npcs = {}
        for line in str(self.event_lists[0]).split('\n'):
            if not ('. 68(' in line or '. 7B(' in line.upper()):
                continue
            match = npc_preload_matcher.match(line)
            if not match:
                continue
            npc_index, sprite = match.groups()
            npc_index = '{0:0>2X}'.format(int(npc_index, 0x10) - 0x4f)
            if npc_index in preload_npcs and preload_npcs[npc_index] != sprite:
                preload_npcs[npc_index] = 'VARIOUS'
            else:
                preload_npcs[npc_index] = sprite
        for npc_index, sprite in sorted(preload_npcs.items()):
            check = 'NPC %s' % npc_index
            index = s2.index(check)
            eol = s2[index:].index('\n') + index
            s2 = s2[:eol] + ' PRELOAD %s' % sprite + s2[eol:]
            assert index > 0
        s = '{0}\n{1}\n{2}\n'.format(s1.strip(), s2.strip(), s3.strip())
        s = s.strip()
        if '\n' in s:
            s += '\n'
        for el in self.event_lists:
            elstr = str(el).rstrip()
            if not elstr:
                continue
            s += '\n' + elstr + '\n'
        matcher = re.compile('\[{0:0>2X}-.-..\]'.format(self.index))
        matches = matcher.findall(s)
        for match in matches:
            checkstr = 'EVENT %s' % match[1:-1]
            if checkstr not in s:
                s = s.replace(' %s' % match, '')
        s = s.replace('\n', '\n  ')
        while '\n\n\n' in s:
            s = s.replace('\n\n\n', '\n\n')

        return s.strip()

    @cached_property
    def name(self):
        pointer = self.base_pointer + self.map_name_pointer
        f = get_open_file(self.filename)
        f.seek(pointer)
        name = b''
        while True:
            c = f.read(1)
            if c == b'\x00':
                break
            name += c
        name, _ = self.parse_name(data=name, repeat_pointer=0x38000)
        return self.prettify_text(name)

    @clached_property
    def ALL_POINTERS(self):
        all_pointers = set()
        for meo in MapEventObject.every:
            for el in meo.event_lists:
                sps = {p for (i, p) in el.script_pointers}
                all_pointers |= sps
                all_pointers.add(el.pointer)
            all_pointers.add(meo.eventlists_pointer)
            assert meo.npc_pointer in all_pointers
        all_pointers.add(self.END_EVENT_POINTER)
        all_pointers.add(self.END_NPC_POINTER)
        return all_pointers

    @clached_property
    def MIN_EVENT_LIST(self):
        return min(meo.eventlists_pointer for meo in MapEventObject.every)

    @property
    def map_meta(self):
        return MapMetaObject.get(self.index)

    @cached_property
    def base_pointer(self):
        assert self.pointer & 0xff8000 == 0x38000
        return self.pointer & 0xff8000

    @property
    def eventlists_pointer(self):
        pointer = (self.eventlist_highbyte << 15) | self.eventlist_lowbytes
        return self.base_pointer + pointer

    def set_eventlists_pointer(self, pointer):
        temp = pointer - self.base_pointer
        self.eventlist_highbyte = temp >> 15
        self.eventlist_lowbytes = temp & 0x7fff
        assert self.eventlists_pointer == pointer

    @property
    def npc_pointer(self):
        pointer = (self.npc_highbyte << 15) | self.npc_lowbytes
        return self.base_pointer + pointer

    def set_npc_pointer(self, pointer):
        temp = pointer - self.base_pointer
        self.npc_highbyte = temp >> 15
        self.npc_lowbytes = temp & 0x7fff
        assert self.npc_pointer == pointer

    def get_eventlist_by_index(self, index):
        candidates = [el for el in self.event_lists if el.index == index]
        assert len(candidates) == 1
        return candidates[0]

    @property
    def event_pointers(self):
        listed_event_pointers = [p for (pointer, elist) in self.event_lists
                                 for (i, p) in elist]
        return listed_event_pointers

    @classmethod
    def deallocate(self, to_deallocate):
        if isinstance(to_deallocate, tuple):
            to_deallocate = {to_deallocate}
        temp = sorted(set(self.FREE_SPACE) | to_deallocate)
        while True:
            temp = sorted(temp)
            for ((a1, b1), (a2, b2)) in zip(temp, temp[1:]):
                assert a1 <= a2
                assert a1 < b1
                assert a2 < b2
                if a1 <= a2 <= b1:
                    temp.remove((a1, b1))
                    temp.remove((a2, b2))
                    temp.append((min(a1, a2), max(b1, b2)))
                    break
            else:
                break

        self.FREE_SPACE = sorted(temp)

    @classmethod
    def allocate(self, length, npc_loader=False, near=None,
                 find_best_fit_dry=False, forced=None):
        if npc_loader:
            candidates = [(a, b) for (a, b) in self.FREE_SPACE
                          if a < self.MIN_EVENT_LIST and (b-a) >= length]
        else:
            candidates = [(a, b) for (a, b) in self.FREE_SPACE
                          if a >= self.MIN_EVENT_LIST and (b-a) >= length]

        if forced is not None:
            candidates = [(a, b) for (a, b) in candidates if a == forced]
        if near is not None:
            if not isinstance(near, list):
                near = [near]
            for n in near:
                candidates = [(a, b) for (a, b) in candidates
                              if 0 <= a - n <= 0x7fff]

        if not candidates:
            raise Exception('Not enough free space.')

        if find_best_fit_dry:
            candidates = sorted(candidates, key=lambda x: (x[1]-x[0], x))
            a, b = candidates.pop(0)
            return a

        a, b = candidates.pop(0)
        remaining = (a+length, b)
        assert remaining[0] <= remaining[1]
        self.FREE_SPACE.remove((a, b))
        if remaining[0] < remaining[1]:
            self.FREE_SPACE.append(remaining)
        self.FREE_SPACE = sorted(self.FREE_SPACE)
        return a

    @classmethod
    def parse_name(self, data, repeat_pointer):
        text = []
        text.append((None, b''))
        while True:
            try:
                textcode, data = data[0], data[1:]
            except IndexError:
                break
            if textcode in self.TEXT_TERMINATORS:
                text.append((textcode, b''))
                break
            elif textcode == 0xa:
                n = self.TEXT_PARAMETERS[textcode]
                text_parameters, data = data[:n], data[n:]
                value = int.from_bytes(text_parameters, byteorder='little')
                length = (value >> 12) + 2
                pointer = value & 0xfff
                p = repeat_pointer + pointer
                f = get_open_file(get_outfile())
                f.seek(p)
                repeat_text = f.read(length)
                text.append((None, repeat_text))
            elif textcode in self.TEXT_PARAMETERS:
                n = self.TEXT_PARAMETERS[textcode]
                text_parameters, data = data[:n], data[n:]
                text.append((textcode, text_parameters))
            else:
                if text[-1][0] is not None:
                    text.append((None, b''))
                a, b = text.pop()
                assert a is None
                b += bytes([textcode])
                text.append((a, b))
        text = [(a, b) for (a, b) in text if b or (a is not None)]
        for a, b in zip(text, text[1:]):
            if a is None:
                assert b is not None
        return text, data

    @classmethod
    def prettify_text(self, text_script):
        s = ''
        for opcode, parameters in text_script:
            if opcode in {5, 6}:
                index = parameters[0]
                index += (0x100 * (opcode-5))
                word = WordObject.get(index).word
                s += word
            elif opcode in self.TEXT_TERMINATORS:
                if opcode in self.CHARACTER_MAP:
                    s += self.CHARACTER_MAP[opcode]
                else:
                    s += '<END MESSAGE>'.format(opcode)
            elif opcode == 'NPC':
                assert len(parameters) == 1
                s += '<VOICE {0:0>2X}>'.format(parameters[0])
            elif opcode == 'POSITION':
                assert len(parameters) == 2
                s += '<POSITION {0}>'.format(hexify(parameters))
            elif opcode == 'COMMENT':
                s += '<{0}>'.format(parameters)
            elif opcode is None:
                for c in parameters:
                    if c in self.CHARACTER_MAP:
                        s += self.CHARACTER_MAP[c]
                    elif c & 0x80:
                        index = c & 0x7F
                        try:
                            w = WordObject.get(index + 0x200)
                            s += w.word
                        except KeyError:
                            s += '<{0:0>2X}>'.format(c)
                    else:
                        if chr(c) in self.ASCII_VISIBLE:
                            s += chr(c)
                        else:
                            s += '<{0:0>2X}>'.format(c)
            elif opcode in self.CHARACTER_MAP:
                sub = self.CHARACTER_MAP[opcode]
                assert sub[-1] == '>'
                if parameters:
                    sub = sub.rstrip('>')
                    sub = '{0} {1}>'.format(sub, hexify(parameters))
                s += sub
            elif isinstance(opcode, str):
                s += '<{0} {1}>'.format(opcode, hexify(parameters))
            else:
                raise Exception('Unhandled text opcode %x.' % opcode)
        return s

    @classmethod
    def reverse_prettify_text(self, message, compress=True):
        reverse_keys = sorted(self.REVERSE_CHARACTER_MAP,
                              key=lambda k: (-len(k), k))
        parameters = [message]
        while True:
            reset_flag = False
            for i, p in list(enumerate(parameters)):
                if not isinstance(p, str):
                    continue
                if len(p) == 2 and p[0] in '\x05\x06':
                    continue
                for k in reverse_keys:
                    if k in p:
                        p1, p2 = p.split(k, 1)
                        parameters = (parameters[:i] +
                                      [p1, self.REVERSE_CHARACTER_MAP[k], p2] +
                                      parameters[i+1:])
                        reset_flag = True
                        break
                if reset_flag:
                    break
                match = self.TAG_MATCHER.search(p)
                if match:
                    k = match.group(0)
                    values = [int(v, 0x10) for v in match.group(2).split('-')]
                    label = '<%s>' % match.group(1)
                    if label in self.REVERSE_CHARACTER_MAP:
                        values.insert(0, self.REVERSE_CHARACTER_MAP[label])
                    p1, p2 = p.split(k, 1)
                    parameters = (parameters[:i] + [p1] + values + [p2] +
                                  parameters[i+1:])
                    break
                if not compress:
                    continue
                new_p = WordObject.compress(p)
                assert isinstance(new_p, list)
                if len(new_p) == 1 and new_p[0] == p:
                    continue
                parameters = parameters[:i] + new_p + parameters[i+1:]
                break
            else:
                if not reset_flag:
                    break
        for p in parameters:
            if isinstance(p, str):
                if len(p) == 2 and p[0] in '\x05\x06':
                    continue
                assert '<' not in p and '>' not in p
        parameters = [p if isinstance(p, str) else chr(p)
                      for p in parameters if p != '']
        result = bytes([ord(c) for c in ''.join(parameters)])
        return result

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)

        self.event_lists = [self.EventList(self.npc_pointer, self)]

        f = get_open_file(self.filename)
        f.seek(self.eventlists_pointer)
        self.unknown = int.from_bytes(f.read(2), byteorder='little')
        for i in range(6):
            f.seek(self.eventlists_pointer + 2 + (i*2))
            relative_pointer = int.from_bytes(f.read(2), byteorder='little')
            absolute_pointer = self.eventlists_pointer + relative_pointer
            el = self.EventList(absolute_pointer, self)
            self.event_lists.append(el)

        self.deallocate((self.eventlists_pointer,
                         self.eventlists_pointer + 14))
        assert len(self.event_lists) == 7

    def preprocess(self):
        assert not hasattr(self, 'event_associations')
        for el in self.event_lists:
            el.read_scripts()

    @classmethod
    def full_cleanup(self):
        f = get_open_file(get_outfile())
        for (a, b) in self.FREE_SPACE:
            f.seek(a)
            f.write(b'\x00' * (b-a))
        super().full_cleanup()

    def write_data(self, filename=None, pointer=None):
        f = get_open_file(get_outfile())
        self.set_eventlists_pointer(self.allocate(14, npc_loader=False))
        f.seek(self.eventlists_pointer)
        f.write(self.unknown.to_bytes(2, byteorder='little'))

        empty_eventlist = None
        for (i, el) in enumerate(self.event_lists):
            if (el.index != 'X' and len(el.scripts) == 0
                    and empty_eventlist is not None):
                el.pointer = empty_eventlist
            else:
                el.write()
                if el.index != 'X' and len(el.scripts) == 0:
                    empty_eventlist = el.pointer

            if el.index == 'X':
                self.set_npc_pointer(el.pointer)
                continue

            relative_pointer = el.pointer - self.eventlists_pointer
            f.seek(self.eventlists_pointer + (i * 2))
            f.write(relative_pointer.to_bytes(2, byteorder='little'))
        assert f.tell() == self.eventlists_pointer + 14
        super().write_data(filename, pointer)


def randomize_rng():
    # haven't quite figured out how this works
    # but certain values crash the game
    a = random.randint(0, 0xFF)
    b = 1
    f = get_open_file(get_outfile())
    f.seek(addresses.rng1)
    f.write(chr(a))
    f.seek(addresses.rng2)
    f.write(chr(b))


def patch_events(filenames=None, **kwargs):
    if filenames is None:
        filenames = []
        for label in EVENT_PATCHES:
            filenames.append(label)
            filename = path.join(tblpath, 'eventpatch_{0}.txt'.format(label))

    if not filenames:
        return

    if not isinstance(filenames, list):
        filenames = [filenames]
    filenames = [fn if fn.endswith('.txt') else
                 path.join(tblpath, 'eventpatch_{0}.txt'.format(fn))
                 for fn in filenames]

    to_import = {}
    identifier = None
    script_text = None
    for filename in filenames:
        for line in read_lines_nocomment(filename):
            line = line.lstrip()
            if line.startswith('EVENT'):
                if identifier is not None:
                    assert identifier not in to_import
                    to_import[identifier] = script_text
                identifier = line.split(' ')[-1]
                script_text = ''
            else:
                script_text = '\n'.join([script_text, line])
    assert identifier not in to_import
    to_import[identifier] = script_text
    for identifier, script_text in sorted(to_import.items()):
        map_index, el_index, script_index = identifier.split('-')
        map_index = int(map_index, 0x10)
        script_index = (None if script_index == 'XX'
                        else int(script_index, 0x10))
        meo = MapEventObject.get(map_index)
        el = meo.get_eventlist_by_index(el_index)
        script = el.get_script_by_index(script_index)
        script.import_script(script_text, **kwargs)


def route_items():
    ir = ItemRouter(path.join(tblpath, 'requirements.txt'),
                    path.join(tblpath, 'restrictions.txt'))
    while True:
        unassigned = {x for xs in ir.unassigned_items for x in xs}
        ir.assign_everything()
        print(ir.report)
        ir.clear_assignments()
        break


def dump_events(filename):
    s = ''
    for meo in MapEventObject.every:
        s += str(meo) + '\n\n'

    with open(filename, 'w+') as f:
        f.write(s)

    return s


ALL_OBJECTS = [g for g in globals().values()
               if isinstance(g, type) and issubclass(g, TableObject)
               and g not in [TableObject]]


if __name__ == '__main__':
    try:
        print ('You are using the Lufia II '
               'randomizer version %s.\n' % VERSION)

        codes = {
            'airship': ['airship'],
            'anywhere': ['anywhere'],
            #'everywhere': ['everywhere'],
            'personnel': ['nothingpersonnelkid', 'nothing.personnel.kid',
                          'nothing personnel kid', 'nothing_personnel_kid'],
            'easymodo': ['easymodo'],
        }
        run_interface(ALL_OBJECTS, snes=True, codes=codes, custom_degree=True)
        numify = lambda x: '{0: >3}'.format(x)
        minmax = lambda x: (min(x), max(x))

        if 'airship' in get_activated_codes():
            print('AIRSHIP CODE ACTIVATED')
            if '_JP' in get_global_label():
                write_patch(get_outfile(), 'patch_start_airship_jp.txt')
            else:
                write_patch(get_outfile(), 'patch_start_airship.txt')

        if 'personnel' in get_activated_codes():
            print('NOTHING PERSONNEL KID.')

        patch_events()

        route_items()
        patch_events('max_world_clock')
        patch_events('max_world_clock_manual')
        patch_events('open_world_base')
        MapEventObject.roaming_comments = set()

        clean_and_write(ALL_OBJECTS)
        dump_events('_l2r_event_dump.txt')

        rewrite_snes_meta('L2-R', int(VERSION[0]), lorom=True)
        finish_interface()
    except Exception:
        print(format_exc())
        input('Press Enter to close this program.')
