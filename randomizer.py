from randomtools.tablereader import (
    TableObject, get_global_label, get_seed, tblpath, addresses, names,
    get_random_degree, mutate_normal, shuffle_normal, shuffle_simple,
    get_difficulty, get_open_file, write_patch)
from randomtools.utils import (
    map_to_lorom, map_from_lorom,
    classproperty, cached_property, clached_property,
    read_lines_nocomment, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)
from randomtools.itemrouter import ItemRouter, ItemRouterException

from collections import defaultdict, Counter, namedtuple
from copy import deepcopy
from math import floor
from os import path
import re
from string import ascii_letters, digits, punctuation, printable
from traceback import format_exc


VERSION = '3.9'
TEXT_VERSION = 'Three Nine'
ALL_OBJECTS = None
DEBUG_MODE = False

scalecustom_boss = None
scalecustom_nonboss = None


def hexify(s):
    return '-'.join('{0:0>2X}'.format(c) for c in s)


def lange(low, high):
    return list(range(low, high))


EVENT_PATCHES = [
    'skip_tutorial',
    'treadool_warp',
]


def check_open_world():
    if any(code in get_activated_codes() for code in
            {'open', 'airship', 'custom'}) or 'w' in get_flags():
        return True
    return False


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
            ptr = max([self.pointer]+list(self.additional_addresses.values()))
            assert ptr + 2 <= n.pointer

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


class MapFormationsObject(TableObject):
    def __repr__(self):
        s = '\n'.join(['{0:0>2X}: {1}'.format(i, f)
                       for (i, f) in enumerate(self.formations)])
        return 'MAP FORMATIONS {0:0>2X}\n{1}'.format(self.index, s)

    @classproperty
    def base_pointer(self):
        assert self.specs.pointer == 0xbb9ac
        return self.specs.pointer

    @classproperty
    def all_pointers(self):
        if hasattr(MapFormationsObject, '_all_pointers'):
            return MapFormationsObject._all_pointers

        all_pointers = {
            mfo.reference_pointer + MapFormationsObject.base_pointer
            for mfo in MapFormationsObject.every}
        MapFormationsObject._all_pointers = sorted(all_pointers)
        return MapFormationsObject.all_pointers

    @property
    def formations_pointer(self):
        return self.base_pointer + self.reference_pointer

    @property
    def num_formations(self):
        index = self.all_pointers.index(self.formations_pointer)
        try:
            next_pointer = self.all_pointers[index+1]
        except IndexError:
            return 0
        return next_pointer - self.formations_pointer

    @property
    def formations(self):
        self.preprocess()
        return [FormationObject.get(i) for i in self.formation_indexes]

    def preprocess(self):
        if hasattr(self, 'formation_indexes'):
            return
        f = get_open_file(get_outfile())
        f.seek(self.formations_pointer)
        self.formation_indexes = list(map(int, f.read(self.num_formations)))

    def write_data(self, filename=None, pointer=None):
        super().write_data(filename, pointer)
        if self.num_formations <= 0:
            return
        f = get_open_file(get_outfile())
        f.seek(self.formations_pointer)
        f.write(bytes(self.formation_indexes))


class FormationObject(TableObject):
    custom_random_enable = 'f'

    UNUSED_FORMATIONS = [0xA5]

    def __repr__(self):
        ss = []
        for i, m in enumerate(self.monsters):
            if m is not None:
                ss.append('#{0} {1:0>2X}-{2}'.format(i+1, m.index, m.name))
        ss = ', '.join(ss)
        return 'FORMATION {0:0>2X}: {1}'.format(self.index, ss)

    @cached_property
    def monsters(self):
        return [MonsterObject.get(index) if index < 0xFF else None
                for index in self.monster_indexes]

    @cached_property
    def clean_monsters(self):
        return [m for m in self.monsters if m is not None]

    @property
    def rank(self):
        if self.monsters[0] is None:
            return -1
        return self.monsters[0].rank

    def guess_sprite(self):
        if self.monsters[0] is None:
            return None
        return self.monsters[0].guess_sprite()

    def preprocess(self):
        self.monsters

class BossFormationObject(TableObject):
    custom_random_enable = 'b'

    GROUND_LEVEL = 0x68
    CENTER_LINE = 0xa0
    DUMMIED_MONSTERS = [0x60, 0x99]
    BANNED_MONSTERS = [0xd3, 0xdf]

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

    @property
    def details(self):
        s = str(self)
        coordinates = ['({0:0>2x},{1:0>2x})'.format(x, y)
                       for (x, y) in self.monster_coordinates]
        coordinates = ' '.join(coordinates)
        return '{0}\n{1}\n{2}'.format(s, coordinates, hexify(self.unknown))

    @property
    def monsters(self):
        return [MonsterObject.get(i) for i in self.monster_indexes
                if i != 0xFF]

    @property
    def old_monsters(self):
        return [MonsterObject.get(i) for i in self.old_data['monster_indexes']
                if i != 0xFF]

    @property
    def memory_load(self):
        sprite_metas = {m.sprite_meta for m in self.monsters}
        load = sum([m.memory_load for m in sprite_metas])
        return load

    @property
    def rank(self):
        return (max(m.rank for m in self.monsters)
                * sum(m.hp for m in self.monsters))

    @classproperty
    def uniques(self):
        pointers = {bfo.reference_pointer for bfo in BossFormationObject.every}
        uniques = [bfo for bfo in BossFormationObject.every
                   if bfo.index > 0]
        assert len(uniques) == len(pointers)
        return uniques

    @property
    def boss(self):
        return max(self.monsters, key=lambda m: (m.rank, m.index))

    def guess_sprite(self):
        return self.boss.guess_sprite()

    def guess_bgm(self):
        return 0x19

    def become_random(self, seed_monster=None):
        for bfo in BossFormationObject.uniques:
            if (bfo.index != self.index
                    and bfo.reference_pointer == self.reference_pointer):
                raise Exception(
                    'Conflict: Boss Formation {0:0>2X}.'.format(self.index))
        valid_monsters = [m for m in MonsterObject.every
                          if m.index not in self.BANNED_MONSTERS]
        self.unknown = self.get(1).old_data['unknown']
        if seed_monster is None:
            seed_monster = random.choice(valid_monsters)
        same_sprite_monsters = {
            m for m in valid_monsters
            if m.battle_sprite == seed_monster.battle_sprite}
        same_formation_monsters = set()
        for f in FormationObject.every:
            if seed_monster in f.monsters:
                for m in f.monsters:
                    if m is not None:
                        same_formation_monsters.add(m)
        for bfo in BossFormationObject.uniques:
            if seed_monster in bfo.old_monsters:
                for m in bfo.old_monsters:
                    same_formation_monsters.add(m)
        distant_relatives = set()
        for cousin in same_sprite_monsters | same_formation_monsters:
            distant_relatives.add(cousin)
            for f in FormationObject.every:
                if cousin in f.monsters:
                    for m in f.monsters:
                        if m is not None:
                            distant_relatives.add(m)
            for bfo in BossFormationObject.uniques:
                if cousin in bfo.old_monsters:
                    for m in bfo.old_monsters:
                        distant_relatives.add(m)
        wildcard = random.choice(valid_monsters)
        candidates = (sorted(same_sprite_monsters) +
                      sorted(same_formation_monsters) +
                      sorted(distant_relatives) +
                      [seed_monster, wildcard])
        candidates = sorted(candidates, key=lambda m: m.index)
        candidates = [c for c in candidates
                      if c.sprite_meta.memory_load <= 128]

        chosen_monsters = [seed_monster]
        memory_load = seed_monster.sprite_meta.memory_load
        MEMORY_LOAD_LIMIT = 256
        candidates.append(None)
        while True:
            if not candidates:
                break
            if len(set(chosen_monsters)) >= 3:
                candidates = [c for c in candidates
                              if c in chosen_monsters or c is None]
            sprite_metas = {m.sprite_meta for m in chosen_monsters}
            chosen = random.choice(candidates)
            if chosen is None:
                break
            if (memory_load + chosen.sprite_meta.memory_load
                    > MEMORY_LOAD_LIMIT):
                break
            chosen_monsters.append(chosen)
            memory_load += chosen.sprite_meta.memory_load
            if len(chosen_monsters) >= 6:
                break

        chosen_monsters = sorted(chosen_monsters,
                                 key=lambda m: (-m.rank, m.signature))
        monster_indexes = []
        monster_coordinates = []

        RIGHT_BORDER_MARGIN = 8
        MAX_WIDTH = 224
        if len(chosen_monsters) > 1:
            total_width = sum([m.width for m in chosen_monsters])
            divisor = len(chosen_monsters) - 1
            margin = int(floor((MAX_WIDTH - total_width) / divisor))
            margin = min(margin, 8)
            assert total_width + (margin*(len(chosen_monsters)-1)) <= MAX_WIDTH
        else:
            margin = 0

        farthest_left = 0
        farthest_right = 0
        companion_coordinates = set()
        previous_monster = None
        current_side = 'right'
        for m in chosen_monsters:
            if previous_monster is not None:
                if current_side and previous_monster is not m:
                    if current_side == 'left':
                        current_side = 'right'
                    else:
                        current_side = 'left'
                if current_side is None:
                    current_side = 'right'
                if current_side == 'right':
                    x = farthest_right + margin
                else:
                    x = farthest_left - (m.width + margin)
            else:
                x = 0-(m.width//2)

            if m.height < self.GROUND_LEVEL:
                y = self.GROUND_LEVEL - m.height
            else:
                y = 0x80 - m.height

            farthest_left = min(x, farthest_left)
            farthest_right = max(x+m.width, farthest_right)
            monster_indexes.append(m.index)
            monster_coordinates.append((x, y))
            previous_monster = m

        width_with_margins = farthest_right - farthest_left
        extra_space = MAX_WIDTH - width_with_margins
        right_margin = RIGHT_BORDER_MARGIN + (extra_space//2)
        offset = (0x100-farthest_right) - right_margin
        monster_coordinates = [(x + offset, y)
                               for (x, y) in monster_coordinates]
        assert all([0 <= x <= 0xFF and 0 <= y <= 0xFF
                    for (x, y) in monster_coordinates])

        self.monster_indexes = []
        self.monster_coordinates = []
        for ((x, y), i) in sorted(zip(monster_coordinates, monster_indexes)):
            self.monster_indexes.append(i)
            self.monster_coordinates.append((x, y))

        while len(self.monster_indexes) < 6:
            assert len(self.monster_coordinates) == len(self.monster_indexes)
            self.monster_indexes.append(0xFF)
            self.monster_coordinates.append((0, 0))

        if hasattr(self, '_property_cache'):
            del(self._property_cache)

    def write_data(self, filename=None, pointer=None):
        base_pointer = self.specs.pointer
        formation_pointer = base_pointer + self.reference_pointer
        f = get_open_file(get_outfile())
        f.seek(formation_pointer)
        f.write(bytes(self.monster_indexes))
        for (x, y) in self.monster_coordinates:
            f.write(bytes([x, y]))
        f.write(self.unknown)
        super().write_data(filename, pointer)

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
        # THEORIES
        # first byte: idle/attack animations?
        # next four bytes: party splitting for pierre & daniele?
        # sixth byte boss death animation
        # seventh byte: special event for pierre, daniele, master jelly?
        # last five bytes: always 03-01-01-02-00
        self.unknown = f.read(12)
        self.old_data['monster_indexes'] = self.monster_indexes
        self.old_data['monster_coordinates'] = self.monster_coordinates
        self.old_data['unknown'] = self.unknown


class SpriteMetaObject(TableObject):
    @property
    def height(self):
        return self.height_misc & 0x1f

    @property
    def memory_load(self):
        return self.height * self.width


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

    chest_maps = {}
    for line in read_lines_nocomment(path.join(tblpath, 'chest_maps.txt')):
        chest_index, map_index, _ = line.split(' ', 2)
        chest_index = int(chest_index, 0x10)
        map_index = int(map_index, 0x10)
        assert chest_index not in chest_maps
        chest_maps[chest_index] = map_index

    def __repr__(self):
        s = 'CHEST {0:0>2X}: {1:0>6x}-{2:0>3X} {3}'.format(
            self.index, self.pointer, self.item_index,
            self.item.name)
        return s

    @property
    def item_index(self):
        return (
            self.get_bit('item_high_bit') << 8) | self.item_low_byte

    @property
    def old_item_index(self):
        return ((self.get_bit('item_high_bit', old=True) << 8)
                | self.old_data['item_low_byte'])

    @property
    def map_index(self):
        return ChestObject.chest_maps[self.index]

    @property
    def item(self):
        return ItemObject.get(self.item_index)

    @property
    def old_item(self):
        return ItemObject.get(self.old_item_index)

    @staticmethod
    def get_chests_by_map_index(map_index):
        return [c for c in ChestObject.every if c.map_index == map_index]

    def set_item(self, item):
        if isinstance(item, ItemObject):
            item = item.index
        if item & 0x100:
            self.set_bit('item_high_bit', True)
        else:
            self.set_bit('item_high_bit', False)
        self.item_low_byte = item & 0xFF

    def mutate(self):
        if self.item.rank < 0:
            return
        candidates = [
            i for i in ItemObject.ranked if i.rank >= 0 and
            i.get_bit('equipable') == self.item.get_bit('equipable')]
        i = self.item.get_similar(candidates)
        self.set_item(i)

    @classmethod
    def intershuffle(cls, candidates=None, random_degree=None):
        cls.class_reseed("inter")
        zonedict = defaultdict(list)
        dragon_egg = ItemObject.get(0x2b)
        for c in ChestObject.every:
            if c.item.rank >= 0 or c.item == dragon_egg:
                meo = MapEventObject.get(c.map_index)
                zonedict[meo.zone_index].append(c)

        for zone_index in sorted(zonedict.keys()):
            chests = zonedict[zone_index]
            if len(chests) <= 1:
                continue

            if not check_open_world():
                shuffled_items = sorted([c.item for c in chests],
                                        key=lambda i: i.index)
                random.shuffle(shuffled_items)
                for (chest, item) in zip(chests, shuffled_items):
                    chest.set_item(item)

            if check_open_world():
                dragon_egg_chests = [c for c in chests if c.item == dragon_egg]
                for dec in dragon_egg_chests:
                    other = random.choice(chests)
                    dec_index = dec.item.index
                    other_index = other.item.index
                    dec.set_item(other_index)
                    other.set_item(dec_index)

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
            self.characters |= 0x7f
            self.mp_cost = 0
        if 's' not in get_flags() and 'l' not in get_flags():
            return
        self.price_clean()


class CharLevelObject(TableObject): pass
class CharExpObject(TableObject): pass
class CapsuleLevelObject(TableObject): pass


class InitialEquipObject(TableObject):
    def __repr__(self):
        s = '{0}\n'.format(self.character_name)
        for (attr, _, _) in self.specs.attributes:
            i = ItemObject.get(getattr(self, attr))
            s += '{0:6} - {1:0>2x} {2}\n'.format(attr, i.index, i.name)
        return s.strip()

    @property
    def equips(self):
        return [ItemObject.get(getattr(self, attr))
                for (attr, _, _) in self.specs.attributes]

    @property
    def character_name(self):
        return CharacterObject.get(self.index).name

    def clear_initial_equipment(self):
        for attr in self.old_data:
            setattr(self, attr, 0)

    def set_appropriate_initial_equipment(self):
        self.clear_initial_equipment()
        items = [i for i in ItemObject.every if i.is_buyable
                 and i.get_bit('equipable')
                 and i.get_bit(self.character_name.lower())
                 and not i.is_coin_item]
        items = sorted(items, key=lambda i: (i.price, i.signature))
        for attr in ['weapon', 'armor', 'shield', 'helmet']:
            candidates = [i for i in items if i.get_bit(attr)]
            if candidates:
                setattr(self, attr, candidates[0].index)


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

    OVERWORLD_SPRITE_TABLE_FILENAME = path.join(
        tblpath, 'monster_overworld_sprites.txt')
    monster_overworld_sprites = {}
    for line in read_lines_nocomment(OVERWORLD_SPRITE_TABLE_FILENAME):
        monster_index, sprite_index, name = line.split(' ', 2)
        monster_index = int(monster_index, 0x10)
        sprite_index = int(sprite_index, 0x10)
        monster_overworld_sprites[monster_index] = sprite_index

    @property
    def intershuffle_valid(self):
        return (self.rank >= 0 and not 0xA7 <= self.index <= 0xAA
                and self.index not in [0xdf])

    @cached_property
    def name(self):
        name = self.name_text.decode('utf8').strip()
        return ''.join([c for c in name if c in printable])

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
    def sprite_meta(self):
        return SpriteMetaObject.get(self.battle_sprite-1)

    @property
    def width(self):
        return self.sprite_meta.width * 8

    @property
    def height(self):
        return self.sprite_meta.height * 8

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

    def guess_sprite(self):
        return self.monster_overworld_sprites[self.index]

    def set_drop(self, item):
        if isinstance(item, ItemObject):
            item = item.index
        new_data = self.drop_data & 0xFE00
        self.drop_data = new_data | item

    def set_drop_rate(self, rate):
        new_data = self.drop_data & 0x1FF
        self.drop_data = new_data | (rate << 9)

    def scale_stats(self, scale_amount):
        if 'jelly' in self.name.lower():
            return
        self._scaled = True
        for attr in sorted(self.mutate_attributes):
            value = int(round(getattr(self, attr) * scale_amount))
            setattr(self, attr, value)

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
        for (attr, bytesize, _) in self.specs.attributes:
            if attr in self.mutate_attributes:
                value = getattr(self, attr)
                if attr in ['gold', 'xp']:
                    value = value / get_difficulty()
                else:
                    value = value * get_difficulty()
                value = int(round(value))

                minimum = 0
                maximum = (1<<(bytesize*8))-1
                if not minimum <= value <= maximum:
                    value = min(maximum, max(minimum, value))
                setattr(self, attr, value)

        if self.is_boss and not hasattr(self, '_scaled'):
            for attr in self.mutate_attributes:
                if getattr(self, attr) < self.old_data[attr]:
                    setattr(self, attr, self.old_data[attr])

        if 'easymodo' in get_activated_codes():
            for attr in ['hp', 'attack', 'defense', 'agility', 'intelligence',
                         'guts', 'magic_resistance']:
                setattr(self, attr, 1)


class IPAttackObject(TableObject):
    BANNED_ANIMATIONS = {
        0x84: 0x8a,
        0x8d: 0x83,
        0x8e: 0x87,
        }

    def replace_banned_animation(self):
        if self.animation in self.BANNED_ANIMATIONS:
            self.animation = self.BANNED_ANIMATIONS[self.animation]

    def read_data(self, filename=None, pointer=None):
        super(IPAttackObject, self).read_data(filename, pointer)

        f = get_open_file(get_outfile())
        f.seek(self.pointer+6)
        name = b''
        while True:
            c = f.read(1)
            if c == b'\x00':
                break
            name += c
        self.name = name.decode('ascii')


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
    def is_buyable(self):
        return not self.is_unbuyable

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
            0x1d0: -1,
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
    UNUSED_SHOPS = {0x1a, 0x27}

    def __repr__(self):
        s = 'SHOP %x (%s)\n' % (self.index, self.zone_name)
        s += '{0:0>2X} {1:0>2X} {2:0>2X}\n'.format(
            ord(self.unknown0), self.shop_type, ord(self.unknown2))
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

    @cached_property
    def zone_indexes(self):
        findstr = '. 18({0:0>2X})'.format(self.index)
        zone_indexes = set()
        for meo in MapEventObject.every:
            if findstr in meo.old_pretty:
                zone_indexes.add(meo.zone_index)
        return zone_indexes

    @property
    def zone_name(self):
        if not self.zone_indexes:
            return 'NONE'
        if len(self.zone_indexes) > 1:
            return 'VARIOUS'
        return MapEventObject.zone_names[list(self.zone_indexes)[0]]

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

    @property
    def data_pointer(self):
        return ShopObject.specs.pointer + self.reference_pointer

    def become_coin_shop(self):
        self.unknown0 = b'\x00'
        self.unknown2 = b'\x00'
        self.shop_type = 6

    def read_data(self, filename=None, pointer=None):
        super(ShopObject, self).read_data(filename, pointer)

        if 'shop_type' not in ShopObject.specs.bitnames:
            ShopObject.specs.bitnames['shop_type'] = [
                'pawn', 'coin', 'item', 'weapon', 'armor',
                'spell', 'unk16', 'sell']
        filename = filename or self.filename

        if not hasattr(ShopObject, 'vanilla_buyable_indexes'):
            ShopObject.vanilla_buyable_indexes = set([])

        f = get_open_file(filename)
        f.seek(self.data_pointer)
        self.unknown0 = f.read(1)
        self.shop_type = ord(f.read(1))
        self.unknown2 = f.read(1)
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
        f.seek(self.data_pointer)
        f.write(self.unknown0)
        f.write(bytes([self.shop_type]))
        f.write(self.unknown2)
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
    flag = 'o'
    flag_description = 'monster movements'
    custom_random_enable = True

    def mutate(self):
        movements = [mm.old_data['movement']
                     for mm in MonsterMoveObject.every]
        movements.append(0x1F)
        movements_unique = sorted(set(movements))
        if random.random() <= self.random_degree:
            self.movement = random.choice(movements_unique)
        else:
            self.movement = random.choice(movements)

    def cleanup(self):
        if 'personnel' in get_activated_codes():
            self.movement = 0x1F
        if 'holiday' in get_activated_codes():
            self.movement = 0x1B


class MapMetaObject(TableObject):
    FREE_SPACE = [(0x3e8000, 0x3ec000)]
    IGNORE_EXISTING_DATA = set()

    @classproperty
    def after_order(self):
        return [MapEventObject]

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

    class Exit:
        def __init__(self, data):
            assert len(data) == 9
            self.index = data[0]
            self.boundary_west = data[1]
            self.boundary_north = data[2]
            self.boundary_east = data[3]
            self.boundary_south = data[4]
            self.misc = data[5]
            self.destination_x = data[6]
            self.destination_y = data[7]
            self.destination_map = data[8]

        def __repr__(self):
            height = self.boundary_south - self.boundary_north
            width = self.boundary_east - self.boundary_west
            x = self.boundary_west
            y = self.boundary_north
            if self.destination_map == 0xff:
                destination_map = ''
            else:
                destination_map = '{0:0>2X} {1}'.format(
                    self.destination_map,
                    MapEventObject.get(self.destination_map).name)
            s = '({0:0>2X},{1:0>2X}) -> {2} ({3:0>2X},{4:0>2X})'
            s = s.format(x, y, destination_map,
                         self.destination_x, self.destination_y)
            if not height == width == 1:
                s = '{0} {1}x{2}'.format(s, width, height)
            while '  ' in s:
                s = s.replace('  ', ' ')
            return s

        @property
        def bytecode(self):
            s = []
            for attr in ['index', 'boundary_west', 'boundary_north',
                         'boundary_east', 'boundary_south', 'misc',
                         'destination_x', 'destination_y', 'destination_map']:
                value = getattr(self, attr)
                s.append(value)
            return bytes(s)

    class Tile:
        def __init__(self, data):
            assert len(data) == 5
            self.index = data[0]
            self.boundary_west = data[1]
            self.boundary_north = data[2]
            self.boundary_east = data[3]
            self.boundary_south = data[4]

        def __repr__(self):
            height = self.boundary_south - self.boundary_north
            width = self.boundary_east - self.boundary_west
            x = self.boundary_west
            y = self.boundary_north
            s = '{0:0>2X},{1:0>2X}'
            s = s.format(x, y)
            if not height == width == 1:
                s = '{0} {1}x{2}'.format(s, width, height)
            return s

        @property
        def bytecode(self):
            s = []
            for attr in ['index', 'boundary_west', 'boundary_north',
                         'boundary_east', 'boundary_south']:
                value = getattr(self, attr)
                s.append(value)
            return bytes(s)

    class Waypoint:
        def __init__(self, data):
            assert len(data) == 6
            self.index = data[0]
            self.x = data[1]
            self.y = data[2]
            self.misc = data[3]
            self.offset = int.from_bytes(data[4:], byteorder='little')

        def __repr__(self):
            return '{0:0>2X} ({1:0>2X}) {2:0>2X},{3:0>2X} {4:0>4X}'.format(
                self.index, self.misc, self.x, self.y, self.offset)

        @property
        def bytecode(self):
            s = bytes([self.index, self.x, self.y, self.misc])
            s += int.to_bytes(self.offset, byteorder='little', length=2)
            return s

    @property
    def name(self):
        return MapEventObject.get(self.index).name

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
    def pretty_exits(self):
        s = ''
        for x in self.exits:
            s += '{0:0>2X} ({1:0>2X}) {2}\n'.format(x.index, x.misc, x)
        return s.strip()

    @property
    def pretty_tiles(self):
        s = ''
        for v in self.tiles:
            s += '{0:0>2X} {1}\n'.format(v.index, v)
        return s.strip()

    @property
    def roaming_npcs(self):
        return [exnpc for exnpc in RoamingNPCObject.every
                if exnpc.map_index == self.index]

    @property
    def bytecode(self):
        bytecode = {}
        npc_position_data = b''
        for npc_position in self.npc_positions:
            npc_position_data += npc_position.bytecode
        npc_position_data += b'\xff'
        bytecode[7] = npc_position_data

        exit_data = b''
        for my_exit in self.exits:
            exit_data += my_exit.bytecode
        exit_data += b'\xff'
        bytecode[2] = exit_data

        tile_data = b''
        for tile in self.tiles:
            tile_data += tile.bytecode
        tile_data += b'\xff'
        bytecode[5] = tile_data

        for i in self.old_bytecode:
            if i not in bytecode:
                bytecode[i] = self.old_bytecode[i]

        offset_order = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                        11, 12, 13, 14, 15, 16, 17,
                        10, 19, 20, 18]

        offsets = {}
        for i in sorted(bytecode):
            if i not in offset_order:
                assert bytecode[i] == b'\xff'
                offsets[i] = 0x2c

        bytestring = b'\xff'
        for i in offset_order:
            if i == 8:
                waypoint_offset = len(bytestring) + 0x2c
                waypoint_offset += (6 * len(self.waypoints)) + 1
                waypoint_data = b''
                if self.waypoints:
                    min_offset = min([w.offset for w in self.waypoints])
                for waypoint in self.waypoints:
                    waypoint.offset += waypoint_offset - min_offset
                    waypoint_data += waypoint.bytecode
                waypoint_data += b'\xff' + self.waypoint_shared_data
                bytecode[8] = waypoint_data

            if i != 8 and bytecode[i] in bytestring and bytecode[i] == b'\xff':
                index = bytestring.index(bytecode[i])
            else:
                index = len(bytestring)
                bytestring += bytecode[i]

            index += 0x2c
            offsets[i] = index

        offsets = [offsets[i] for i in sorted(offsets)]
        assert len(offsets) == 21
        offset_str = b''.join([int.to_bytes(o, byteorder='little', length=2)
                               for o in offsets])
        bytestring = offset_str + bytestring
        blocksize = int.to_bytes(
            len(bytestring) + 2, byteorder='little', length=2)
        bytestring = blocksize + bytestring

        # verify the stupid dumb waypoint data structure
        if self.waypoints:
            right = self.waypoints[0].offset
            left = right - 7
            check = self.waypoints[-1].bytecode + b'\xff'
            assert bytestring[left:right] == check
            rightright = right + len(self.waypoint_shared_data)
            assert bytestring[right:rightright] == self.waypoint_shared_data

        return bytestring

    def get_next_npc_index(self):
        if self.npc_positions:
            index = max(npcp.index for npcp in self.npc_positions) + 1
        else:
            index = 1
        return index

    def get_next_exit_index(self):
        if self.exits:
            index = max(x.index for x in self.exits) + 1
        else:
            index = 0
        return index

    def add_npc(self, x, y, boundary=None, misc=0, force_index=None):
        assert x is not None
        assert y is not None
        if boundary:
            ((boundary_west, boundary_north),
                (boundary_east, boundary_south)) = boundary
            boundary_east = x if boundary_east is None else boundary_east
            boundary_west = x if boundary_west is None else boundary_west
            boundary_north = y if boundary_north is None else boundary_north
            boundary_south = y if boundary_south is None else boundary_south
            boundary_east += 1
            boundary_south += 1
        else:
            boundary_west = x
            boundary_north = y
            boundary_east = x + 1
            boundary_south = y + 1
        assert boundary_east > boundary_west
        assert boundary_south > boundary_north
        if force_index:
            index = force_index
        else:
            index = self.get_next_npc_index()
        assert 1 <= index <= 0x20
        bytestr = bytes([index, x, y, boundary_west, boundary_north,
                         boundary_east, boundary_south, misc])
        npcp = self.NPCPosition(bytestr)
        self.npc_positions.append(npcp)
        self.npc_positions = sorted(self.npc_positions, key=lambda x: x.index)
        return npcp

    def add_exit(self, boundary, destination_map, destination_x, destination_y,
                 misc=0xF0, force_index=None):
        if destination_map == self.index:
            destination_map = 0xFF
        ((boundary_west, boundary_north),
            (boundary_east, boundary_south)) = boundary
        boundary_east = x if boundary_east is None else boundary_east
        boundary_west = x if boundary_west is None else boundary_west
        boundary_north = y if boundary_north is None else boundary_north
        boundary_south = y if boundary_south is None else boundary_south
        boundary_east += 1
        boundary_south += 1
        assert boundary_east > boundary_west
        assert boundary_south > boundary_north
        if force_index:
            index = force_index
        else:
            index = self.get_next_exit_index()
        bytestr = bytes([index, boundary_west, boundary_north,
                         boundary_east, boundary_south, misc,
                         destination_x, destination_y, destination_map])
        my_exit = self.Exit(bytestr)
        self.exits.append(my_exit)
        self.exits = sorted(self.exits, key=lambda x: x.index)
        return my_exit

    def add_tile(self, boundary, index):
        ((boundary_west, boundary_north),
            (boundary_east, boundary_south)) = boundary
        bytestr = bytes([index, boundary_west, boundary_north,
                         boundary_east, boundary_south])
        tile = self.Tile(bytestr)
        self.tiles.append(tile)
        self.tiles = sorted(self.tiles, key=lambda t: t.index)

    def add_or_replace_npc(self, x, y, boundary=None, misc=0, index=None):
        if index is None:
            return self.add_npc(x, y, boundary, misc)

        existing = [npcp for npcp in self.npc_positions if npcp.index == index]
        if existing:
            assert len(existing) == 1
            self.npc_positions.remove(existing[0])
        return self.add_npc(x, y, boundary, misc, force_index=index)

    def add_or_replace_exit(self, boundary, destination_map, destination_x,
                            destination_y, misc=0xF0, index=None):
        if index is None:
            return self.add_exit(boundary, destination_map, destination_x,
                                 destination_y, misc)
        existing = [x for x in self.exits if x.index == index]
        if existing:
            assert len(existing) == 1
            self.exits.remove(existing[0])
        return self.add_exit(boundary, destination_map, destination_x,
                             destination_y, misc, force_index=index)

    def add_or_replace_tile(self, boundary, index):
        existing = [t for t in self.tiles if t.index == index]
        if existing:
            assert len(existing) == 1
            self.tiles.remove(existing[0])
        return self.add_tile(boundary, index=index)

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
        self.deallocate((pointer, pointer+blocksize))
        self.old_bytecode = {}

        offsets = []
        for i in range(21):
            i *= 2
            offset = int.from_bytes(data[i+2:i+4], byteorder='little')
            offsets.append(offset)
        sorted_offsets = sorted(set(offsets))

        for i in range(21):
            offset = offsets[i]
            offset_index = sorted_offsets.index(offset)
            if offset_index == len(sorted_offsets)-1:
                next_offset = blocksize
            else:
                next_offset = sorted_offsets[offset_index+1]
            assert next_offset > offset
            offset_data = data[offset:next_offset]
            if offset == 0x2c:
                assert offset_data == b'\xff'
            self.old_bytecode[i] = offset_data

        self.npc_positions = []
        npc_position_data = self.old_bytecode[7]
        assert not (len(npc_position_data)-1) % 8
        assert npc_position_data[-1] == 0xff
        npc_position_data = npc_position_data[:-1]
        while npc_position_data:
            npc_position = self.NPCPosition(npc_position_data[:8])
            npc_position_data = npc_position_data[8:]
            self.npc_positions.append(npc_position)
        self.old_num_npcs = len(self.npc_positions)

        self.exits = []
        exit_data = self.old_bytecode[2]
        assert not (len(exit_data)-1) % 9
        assert exit_data[-1] == 0xff
        exit_data = exit_data[:-1]
        while exit_data:
            my_exit = self.Exit(exit_data[:9])
            exit_data = exit_data[9:]
            self.exits.append(my_exit)
        self.old_num_exits = len(self.exits)

        self.tiles = []
        tile_data = self.old_bytecode[5]
        assert not (len(tile_data)-1) % 5
        assert tile_data[-1] == 0xff
        tile_data = tile_data[:-1]
        while tile_data:
            tile = self.Tile(tile_data[:5])
            tile_data = tile_data[5:]
            self.tiles.append(tile)
        self.old_num_tiles = len(self.tiles)

        self.waypoints = []
        waypoint_data = self.old_bytecode[8]
        while waypoint_data:
            if waypoint_data[0] == 0xff:
                break
            waypoint = self.Waypoint(waypoint_data[:6])
            waypoint_data = waypoint_data[6:]
            self.waypoints.append(waypoint)
        self.waypoint_shared_data = waypoint_data[1:]

    def cleanup(self):
        npcp_indexes = [npcp.index for npcp in self.npc_positions]
        assert len(npcp_indexes) == len(set(npcp_indexes))

    @classmethod
    def full_cleanup(self):
        self.separate_free_space_banks()
        super().full_cleanup()

    @classmethod
    def deallocate(self, to_deallocate):
        if isinstance(to_deallocate, tuple):
            to_deallocate = {to_deallocate}
        old_free_space = set(self.FREE_SPACE)
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
        self.IGNORE_EXISTING_DATA |= (set(self.FREE_SPACE) - old_free_space)

    @classmethod
    def separate_free_space_banks(self):
        f = get_open_file(get_outfile())
        free_space = []
        for (a, b) in self.FREE_SPACE:
            assert b > a
            if not any(a >= a2 and b <= b2
                       for (a2, b2) in self.IGNORE_EXISTING_DATA):
                f.seek(a)
                old_data = f.read(b-a)
                if tuple(set(old_data)) not in {(0,), (0xff,)}:
                    print('WARNING: Address range {0:0>6X}-{1:0>6X} '
                          'designated as free space, but appears to '
                          'be occupied.'.format(a, b))
            while (b & 0xFF8000) > (a & 0xFF8000):
                new_a = (a & 0xFF8000) + 0x8000
                free_space.append((a, new_a))
                a = new_a
            free_space.append((a, b))
        self.FREE_SPACE = free_space

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

class TownSpriteObject(TableObject): pass
class OverPaletteObject(TableObject): pass

class OverSpriteObject(TableObject):
    @staticmethod
    def become_character(character_index):
        maxim = TownSpriteObject.get(0)
        other = TownSpriteObject.get(character_index)
        maxim_ptr = maxim.sprite_pointer
        other_ptr = other.sprite_pointer
        offset = other_ptr - maxim_ptr
        for oso in OverSpriteObject.every:
            oso.sprite_pointer = oso.old_data['sprite_pointer'] + offset

        for opo in OverPaletteObject.every:
            opo.palette_index = other.palette_index * 2

class RoamingNPCObject(TableObject):
    @property
    def sprite_name(self):
        return names.sprites[self.sprite_index]

class EventInstObject(TableObject): pass

class MapEventObject(TableObject):
    flag = 'w'
    flag_description = 'an open world seed'

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
    FREE_SPACE = []

    roaming_comments = set()

    ZONES_FILENAME = 'zones.txt'
    zone_maps = {}
    zone_names = {}
    reverse_zone_map = {}
    for line in read_lines_nocomment(path.join(tblpath, ZONES_FILENAME)):
        line = line.split(' ')
        zone = line[0]
        zone_name = ' '.join(line[1:]).strip()
        zone_index, map_indexes = zone.split(':')
        zone_index = int(zone_index, 0x10)
        map_indexes = [int(m, 0x10) for m in map_indexes.split(',')]
        assert zone_index not in zone_maps
        assert zone_index not in zone_names
        zone_maps[zone_index] = map_indexes
        zone_names[zone_index] = zone_name
        for m in map_indexes:
            assert m not in reverse_zone_map
            reverse_zone_map[m] = zone_index

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
            if len(candidates) == 1:
                return candidates[0]
            return None

        def get_or_create_script_by_index(self, index):
            script = self.get_script_by_index(index)
            if script:
                return script

            script = MapEventObject.Script(None, 0, self, index=index)
            self.scripts.append(script)
            return script

        def read_scripts(self):
            self.scripts = []
            all_pointers = sorted(MapEventObject.ALL_POINTERS)
            for index, p1 in sorted(self.script_pointers):
                p2 = next(p for p in all_pointers if p > p1)
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
                script.realign_addresses()
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

            if not hasattr(self.meo, 'assigned_zero'):
                for i, script in enumerate(self.scripts):
                    if script.index == 0:
                        self.meo.assigned_zero = self.pointer + (i*3)

            for i, script in enumerate(self.scripts):
                data = script.compile(optimize=True, ignore_pointers=True)
                assert data[-1] == 0
                if data[0] == 0 and hasattr(self.meo, 'assigned_zero'):
                    assert data == b'\x00'
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
                    assert b'\x00' in script.data
                    if not hasattr(self.meo, 'assigned_zero'):
                        zero_index = script.data.index(b'\x00')
                        self.meo.assigned_zero = (script.script_pointer
                                                  + zero_index)
                script_pointer = script.script_pointer
                offset = script_pointer - self.meo.eventlists_pointer
                assert 0 <= offset <= 0xffff
                f.seek(self.pointer + (3*i))
                f.write(bytes([script.index]))
                f.write(offset.to_bytes(2, byteorder='little'))
            f.write(b'\xff')
            assert f.tell() == self.pointer + (3 * len(self.scripts)) + 1
            if DEBUG_MODE and hasattr(self.meo, 'assigned_zero'):
                f.seek(self.meo.assigned_zero)
                peek = f.read(1)
                assert peek == b'\x00'

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

        LINE_MATCHER = re.compile('^\s*([0-9a-fA-F]{1,4})\.',
                                  flags=re.MULTILINE)
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

            if self.script_pointer is not None:
                f = get_open_file(get_outfile())
                f.seek(self.script_pointer)
                self.data = f.read(data_length)
            else:
                self.data = b''

            self.old_script_pointer = self.script_pointer
            self.old_base_pointer = self.base_pointer
            self.old_data = self.data
            if self.script_pointer is None:
                self.script_pointer = self.base_pointer

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
            return self.index is None

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
            address_matches = sorted(set(int(match, 0x10)
                                         for match in address_matches))
            done_labels = set()
            for offset in reversed(address_matches):
                if offset in done_labels:
                    continue
                done_labels.add(offset)
                linecode = '{0:0>4X}. '.format(offset)
                try:
                    index = pretty.index(linecode)
                    replacement = '# LABEL @{0:X} ${1:x}\n{2}'.format(
                        offset, self.script_pointer+offset, linecode)
                    pretty = pretty.replace(linecode, replacement)
                except ValueError:
                    to_replace = '@{0:X}'.format(offset)
                    replacement = '@{0:X}!'.format(offset)
                    pretty = pretty.replace(to_replace, replacement)

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

        @staticmethod
        def shift_line_numbers(script_text, offset):
            new_text = []
            for line in script_text.split('\n'):
                if '. ' in line and ('(' in line or ':' in line):
                    line = line.lstrip()
                    if '.' in line[:5] and line[0] != '#':
                        while line[4] != '.':
                            line = '0' + line
                new_text.append(line)
            script_text = '\n'.join(new_text)

            lines = MapEventObject.Script.LINE_MATCHER.findall(script_text)
            for line in lines:
                value = int(line, 0x10)
                assert value < offset
                line = '{0:0>4X}'.format(value)
                replacement = '{0:0>4X}'.format(value + offset)
                script_text = script_text.replace('%s. ' % line.upper(),
                                                  '%s. ' % replacement)
                script_text = script_text.replace('%s. ' % line.lower(),
                                                  '%s. ' % replacement)
            lines = MapEventObject.Script.ADDRESS_MATCHER.findall(script_text)
            lines = sorted(lines, key=lambda l: -int(line, 0x10))
            for line in lines:
                value = int(line, 0x10)
                assert value < offset
                replacement = '{0:X}'.format(value + offset)
                script_text = re.sub('@%s(\W)' % line,
                                     r'@%s\1' % replacement, script_text)
            return script_text

        def prettify_script(self, script):
            if not hasattr(MapEventObject, '_script_cache'):
                MapEventObject._script_cache = {}
            key = str(script)
            if key in MapEventObject._script_cache:
                return MapEventObject._script_cache[key]

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
                        f = BossFormationObject.get(formation_index)
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
                        event = '[{0:0>2X}-B-{1:0>2X}] ({2:0>2X})'.format(
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
                    elif opcode == 0x8C:
                        a = 'Load animation frame {0:0>2X}-{1:0>2X}'.format(
                            parameters[1], parameters[2])
                        b = 'for sprite {0:0>2X}'.format(parameters[0])
                        comment = '{0} {1}'.format(a, b)
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

            MapEventObject._script_cache[key] = pretty.rstrip()
            return self.prettify_script(script)

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
                text.append(('POSITION', unknown))
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

        def import_script(self, text, warn_double_import=True):
            warn_double_import = warn_double_import or DEBUG_MODE
            assert not self.frozen
            if (warn_double_import and
                    hasattr(self, '_imported') and self._imported):
                print('WARNING: Script {0:x} double imported.'.format(
                    self.script_pointer))
            self._imported = True

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
                        print(text)
                        raise Exception(
                            'SCRIPT {0} {1:x} ERR: Lines out of order.'.format(
                                self.signature, self.script_pointer))
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

        def compress(self, text, compress=False):
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

        def normalize_addresses(self):
            line_numbers = [ln for (ln, _, _) in self.script]
            offset = 0 - min(line_numbers)
            if offset == 0:
                return
            new_script = []
            for (l, o, ps) in self.script:
                l += offset
                for p in ps:
                    if isinstance(p, self.Address):
                        p.address += offset
                new_script.append((l, o, ps))
            self.script = new_script

        def realign_addresses(self):
            self.normalize_addresses()
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
                            #compress = opcode not in {0x6d, 0x6e}
                            compress = False
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
            while ' \n' in old:
                old = old.replace(' \n', '\n')
            while ' \n' in new:
                new = new.replace(' \n', '\n')
            old = re.sub('\n..... ', '\n', old)
            new = re.sub('\n..... ', '\n', new)
            old = re.sub('@[^-)]+', '', old)
            new = re.sub('@[^-)]+', '', new)
            old = old.rstrip()
            new = new.rstrip()
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

        def optimize(self):
            addresses = [a.address for (l, o, p) in self.script for a in p
                         if isinstance(a, MapEventObject.Script.Address)]
            new_script = []
            prev_l, prev_o, prev_p = None, None, None
            for line_number, opcode, parameters in self.script:
                if (opcode == 0x69 and opcode == prev_o
                        and line_number not in addresses):
                    new_script.remove((prev_l, prev_o, prev_p))
                    line_number = prev_l
                new_script.append((line_number, opcode, parameters))
                if opcode == 0 and prev_o is None:
                    break
                prev_l, prev_o, prev_p = line_number, opcode, parameters
            self.script = new_script

    # MapEventObject methods
    def __repr__(self):
        s1 = '# MAP {0:0>2X}-{1:0>5x} ({2})'.format(
            self.index, self.pointer, self.name)
        check = '[{0:0>2X}'.format(self.index)
        roamings = [c for c in self.roaming_comments if check in c]
        outroamings = [c for c in roamings if c.startswith(check)]
        inroamings = [c for c in roamings if c not in outroamings]
        s2, s3, s4, s5 = '', '', '', ''
        for c in sorted(inroamings):
            s3 += '# ' + c + '\n'
        for c in sorted(outroamings):
            s5 += '# ' + c + '\n'
        if self.map_meta.exits:
            s1 += '\n' + self.map_meta.pretty_exits
            s1 = s1.replace('\n', '\n# EXIT ') + '\n'
        if self.map_meta.tiles:
            pretty_tiles = self.map_meta.pretty_tiles
            for line in pretty_tiles.split('\n'):
                tile_index = int(line.split()[0], 0x10)
                signature = '{0:0>2X}-D-{1:0>2X}'.format(self.index,
                                                         tile_index)
                s2 += '\n{0} [{1}]'.format(line, signature)
            s2 = s2.replace('\n', '\n# TILE ') + '\n'

        if self.map_meta.npc_positions:
            s4 += '\n' + self.map_meta.pretty_positions
            s4 = s4.replace('\n', '\n# NPC ') + '\n'
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
                if '. 7B(' in line.upper():
                    mfo = MapFormationsObject.get(self.index)
                    formation = mfo.formations[int(npc_index, 0x10)-1]
                    sprite = '{0} ({1})'.format(sprite, formation)
                preload_npcs[npc_index] = sprite
        for npc_index, sprite in sorted(preload_npcs.items()):
            check = 'NPC %s' % npc_index
            try:
                index = s4.index(check)
            except ValueError:
                continue
            eol = s4[index:].index('\n') + index
            s4 = s4[:eol] + ' PRELOAD %s' % sprite + s4[eol:]
            assert index > 0
        s = '{0}\n{1}\n{2}\n{3}\n{4}\n'.format(
            s1.strip(), s2.strip(), s3.strip(), s4.strip(), s5.strip())

        for c in ChestObject.get_chests_by_map_index(self.index):
            s += '# {0}\n'.format(c)

        s = s.strip()
        while '\n\n' in s:
            s = s.replace('\n\n', '\n')
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
        name = self.prettify_text(name, no_opcodes=True)
        return re.sub('<..>', '?', name)

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

    @staticmethod
    def get_script_by_signature(signature):
        meo_index, el_index, script_index = signature.split('-')
        meo = MapEventObject.get(int(meo_index, 0x10))
        el = meo.get_eventlist_by_index(el_index)
        if script_index == 'XX':
            assert el.index == 'X'
            script = el.get_script_by_index(None)
        else:
            script = el.get_script_by_index(int(script_index, 0x10))
        return script

    @property
    def event_pointers(self):
        listed_event_pointers = [p for (pointer, elist) in self.event_lists
                                 for (i, p) in elist]
        return listed_event_pointers

    @property
    def zone_name(self):
        return self.zone_names[self.zone_index]

    @property
    def zone_index(self):
        if self.index in self.reverse_zone_map:
            return self.reverse_zone_map[self.index]
        return None

    def get_zone_enemies(self, old=True):
        sprite_formation_matcher = re.compile(
            '#.*PRELOAD (..) .* \(FORMATION (..):')
        result = []
        for meo in self.neighbors:
            if old:
                s = meo.old_pretty
            else:
                s = str(meo)
            sprite_formations = sprite_formation_matcher.findall(s)
            for sprite, formation in sprite_formations:
                sprite = int(sprite, 0x10)
                formation = FormationObject.get(int(formation, 0x10))
                result.append((sprite, formation))
        return result

    @property
    def neighbors(self):
        if self.zone_index is None:
            return [self]
        return [MapEventObject.get(m)
                for m in sorted(self.zone_maps[self.zone_index])]

    def change_escapability(self, make_escapable=True):
        NO_ESCAPE_BIT = 0x08
        script = self.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(self.index))
        script.optimize()
        new_script = []
        for (l, o, p) in script.script:
            if o == 0x69:
                assert len(p) == 1
                value = p[0]
                no_change = bool(value & NO_ESCAPE_BIT) != make_escapable
                if not no_change:
                    value ^= NO_ESCAPE_BIT
                p = [value]
            new_script.append((l, o, p))
        script.script = new_script

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
    def separate_free_space_banks(self):
        free_space = []
        for (a, b) in self.FREE_SPACE:
            assert b > a
            while (b & 0xFF8000) > (a & 0xFF8000):
                new_a = (a & 0xFF8000) + 0x8000
                free_space.append((a, new_a))
                a = new_a
            free_space.append((a, b))
        self.FREE_SPACE = free_space

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

        candidates = [(a, b) for (a, b) in candidates
                      if a & 0xFF8000 == (a+length-1) & 0xFF8000]

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
        assert a & 0xFF8000 == (a+length-1) & 0xFF8000
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
    def prettify_text(self, text_script, no_opcodes=False):
        s = ''
        for opcode, parameters in text_script:
            if no_opcodes:
                opcode = None
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
                assert 1 <= len(parameters) <= 2
                s += '<POSITION {0}>'.format(hexify(parameters))
            elif opcode == 'COMMENT':
                s += '<{0}>'.format(parameters)
            elif opcode is None:
                for c in parameters:
                    if c in self.CHARACTER_MAP and not no_opcodes:
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
        self.old_pretty = str(self)

    @classmethod
    def full_cleanup(self):
        self.separate_free_space_banks()
        f = get_open_file(get_outfile())
        for (a, b) in self.FREE_SPACE:
            f.seek(a)
            f.write(b'\x00' * (b-a))
        if DEBUG_MODE:
            self._cleanup_text = '\n'.join(
                [str(meo) for meo in MapEventObject.every])
        super().full_cleanup()

    @classmethod
    def purge_orphans(self):
        if not hasattr(MapEventObject, '_cleanup_text'):
            MapEventObject._cleanup_text = '\n'.join(
                [str(meo) for meo in MapEventObject.every])
        for meo in MapEventObject.every:
            for el in meo.event_lists:
                for script in list(el.scripts):
                    if el.index == 'C':
                        find_sig = '[{0}]'.format(script.signature)
                        if find_sig not in MapEventObject._cleanup_text:
                            el.scripts.remove(script)

    def cleanup(self):
        for el in self.event_lists:
            for script in el.scripts:
                script.optimize()
            if el.index == 'X':
                continue
            for script in list(el.scripts):
                if (el.index in 'AD' and
                        {o for (l, o, p) in script.script} == {0}):
                    el.scripts.remove(script)
                    continue

                find_sig = '[{0}]'.format(script.signature)
                if (DEBUG_MODE and el.index in 'CD'
                        and find_sig not in self._cleanup_text):
                    print('WARNING: Orphaned event {0}.'.format(find_sig))

        s = str(self)
        for tile in list(self.map_meta.tiles):
            signature = 'EVENT {0:0>2X}-D-{1:0>2X}'.format(self.index,
                                                           tile.index)
            if signature not in s:
                self.map_meta.tiles.remove(tile)


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


def patch_game_script(patch_script_text, warn_double_import=True):
    to_import = {}
    identifier = None
    script_text = None
    for line in patch_script_text.split('\n'):
        if '#' in line:
            index = line.index('#')
            line = line[:index].rstrip()
        line = line.lstrip()
        if not line:
            continue
        if line.startswith('!'):
            line = line.strip().lower()
            while '  ' in line:
                line = line.replace('  ', ' ')
            if line.startswith('!npc'):
                (command, npc_index, misc, location) = line.split()
                map_index, location = location.split(':')
                a, b = location.split(',')
                map_index = int(map_index, 0x10)
                if npc_index == '+1':
                    npc_index = None
                else:
                    npc_index = int(npc_index, 0x10)
                try:
                    assert misc.startswith('(')
                    assert misc.endswith(')')
                except:
                    raise Exception('Malformed "misc" field: %s' % line)
                misc = int(misc[1:-1], 0x10)
                (x, y, boundary_west, boundary_east, boundary_north,
                    boundary_south) = None, None, None, None, None, None
                for axis, value_range in zip(('x', 'y'), (a, b)):
                    try:
                        assert '>' not in value_range
                        if '<' in value_range:
                            left, middle, right = value_range.split('<=')
                            left = int(left, 0x10)
                            middle = int(middle, 0x10)
                            right = int(right, 0x10)
                            assert left <= middle <= right
                            if axis == 'x':
                                boundary_west = left
                                x = middle
                                boundary_east = right
                            else:
                                assert axis == 'y'
                                boundary_north = left
                                y = middle
                                boundary_south = right
                        else:
                            if axis == 'x':
                                x = int(value_range, 0x10)
                            else:
                                assert axis == 'y'
                                y = int(value_range, 0x10)
                    except:
                        raise Exception('Malformed coordinates: %s' % line)
                boundary = ((boundary_west, boundary_north),
                            (boundary_east, boundary_south))
                MapMetaObject.get(map_index).add_or_replace_npc(
                    x, y, boundary, misc, npc_index)
            elif line.startswith('!exit'):
                try:
                    (command, exit_index, misc,
                        movement, dimensions) = line.split()
                except ValueError:
                    (command, exit_index, misc, movement) = line.split()
                    dimensions = '1x1'
                if exit_index == '+1':
                    exit_index = None
                else:
                    exit_index = int(exit_index, 0x10)
                try:
                    assert misc.startswith('(')
                    assert misc.endswith(')')
                except:
                    raise Exception('Malformed "misc" field: %s' % line)
                misc = int(misc[1:-1], 0x10)

                source, destination = movement.split('->')
                source_index, source_location = source.split(':')
                dest_index, dest_location = destination.split(':')
                boundary_west, boundary_north = source_location.split(',')
                dest_x, dest_y = dest_location.split(',')
                width, height = dimensions.split('x')

                source_index = int(source_index, 0x10)
                dest_index = int(dest_index, 0x10)
                boundary_west = int(boundary_west, 0x10)
                boundary_north = int(boundary_north, 0x10)
                dest_x = int(dest_x, 0x10)
                dest_y = int(dest_y, 0x10)
                width = int(width)
                height = int(height)
                boundary_east = boundary_west + width - 1
                boundary_south = boundary_north + height - 1
                boundary = ((boundary_west, boundary_north),
                            (boundary_east, boundary_south))
                MapMetaObject.get(source_index).add_or_replace_exit(
                    boundary, dest_index, dest_x, dest_y, misc, exit_index)
            elif line.startswith('!tile'):
                try:
                    (command, tile_index, location, dimensions) = line.split()
                except ValueError:
                    (command, tile_index, location) = line.split()
                    dimensions = '1x1'
                map_index, location = location.split(':')
                boundary_west, boundary_north = location.split(',')
                width, height = dimensions.split('x')
                assert tile_index != '+1'
                tile_index = int(tile_index, 0x10)
                map_index = int(map_index, 0x10)
                boundary_west = int(boundary_west, 0x10)
                boundary_north = int(boundary_north, 0x10)
                width = int(width)
                height = int(height)
                boundary_east = boundary_west + width
                boundary_south = boundary_north + height
                boundary = ((boundary_west, boundary_north),
                            (boundary_east, boundary_south))
                MapMetaObject.get(map_index).add_or_replace_tile(
                    boundary, tile_index)
            else:
                raise Exception('Unknown event patch command: %s' % line)
            continue

        if line.startswith('EVENT'):
            while '  ' in line:
                line = line.replace('  ', ' ')
            if identifier is not None:
                assert identifier not in to_import
                to_import[identifier] = script_text
            identifier = line.strip().split(' ')[-1]
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
        script = el.get_or_create_script_by_index(script_index)
        script.import_script(
            script_text, warn_double_import=warn_double_import)


def patch_events(filenames=None, warn_double_import=True):
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

    patch_script_text = ''
    for filename in filenames:
        for line in read_lines_nocomment(filename):
            patch_script_text += line + '\n'
    patch_script_text = patch_script_text.strip()
    patch_game_script(patch_script_text, warn_double_import=warn_double_import)


def patch_with_template(template, parameters, warn_double_import=False):
    if '\n' not in template and '{{' not in template:
        with open(path.join(
                tblpath, 'template_{0}.txt'.format(template))) as f:
            template = f.read()

    for key, value in sorted(parameters.items()):
        if isinstance(value, int):
            value = '{0:0>2X}'.format(value)
            parameters[key] = value

    text = template
    for _ in range(1000):
        for key in sorted(parameters):
            text= text.replace('{{%s}}' % key, parameters[key])
        if '{{' not in text:
            break
    else:
        matcher = re.compile('{{[^{}]*}}')
        matches = sorted(set(matcher.findall(text)))
        raise Exception('Unexpanded template tags: %s' % matches)

    patch_game_script(text, warn_double_import=warn_double_import)

PLAINTEXT_NPC_MATCHER = re.compile(
    '^\s*# NPC (\S\S) \S(\S\S)\S X:(\S*) Y:(\S*) (?:\[(\S*)\] )?'
    'PRELOAD (\S\S) [^:]*(?: .FORMATION (\S\S):.*)?$',
    flags=re.MULTILINE)

class OpenNPCGenerator:
    BOSS_TABLE_FILENAME = path.join(tblpath, 'open_bosses.txt')
    BOSS_LOC_TABLE_FILENAME = path.join(tblpath, 'open_boss_locations.txt')
    REWARD_ITEM_TABLE_FILENAME = path.join(tblpath, 'open_reward_items.txt')
    REWARD_CHAR_TABLE_FILENAME = path.join(tblpath,
                                           'open_reward_characters.txt')
    REWARD_MAIDEN_TABLE_FILENAME = path.join(tblpath,
                                           'open_reward_maidens.txt')
    REWARD_CAPSULE_TABLE_FILENAME = path.join(tblpath,
                                              'open_reward_capsules.txt')

    with open(path.join(tblpath, 'template_reward_item.txt')) as f:
        REWARD_EVENT_ITEM = f.read()
    with open(path.join(tblpath, 'template_reward_character.txt')) as f:
        REWARD_EVENT_CHARACTER = f.read()
    with open(path.join(tblpath, 'template_reward_maiden.txt')) as f:
        REWARD_EVENT_MAIDEN = f.read()
    with open(path.join(tblpath, 'template_reward_capsule.txt')) as f:
        REWARD_EVENT_CAPSULE = f.read()

    boss_properties = {}
    boss_location_properties = {}
    reward_item_properties = {}
    reward_character_properties = {}
    reward_maiden_properties = {}
    reward_capsule_properties = {}

    Boss = namedtuple('Boss', ['name', 'sprite_index_before',
                               'boss_formation_index', 'battle_bgm'])
    for line in read_lines_nocomment(BOSS_TABLE_FILENAME):
        a = Boss(*line.split(','))
        boss_properties[a.name] = a

    BossLocation = namedtuple('BossLocation', ['name', 'map_index',
                              'npc_x', 'npc_y', 'battle_bg', 'map_bgm'])
    for line in read_lines_nocomment(BOSS_LOC_TABLE_FILENAME):
        b = BossLocation(*line.split(','))
        boss_location_properties[b.name] = b

    RewardItem = namedtuple('RewardItem', ['name', 'item_display_name',
                            'item_index', 'item_icon_code'])
    for line in read_lines_nocomment(REWARD_ITEM_TABLE_FILENAME):
        i = RewardItem(*line.split(','))
        reward_item_properties[i.name] = i

    RewardCharacter = namedtuple('RewardCharacter',
        ['name', 'character_display_name', 'character_index'])
    for line in read_lines_nocomment(REWARD_CHAR_TABLE_FILENAME):
        i = RewardCharacter(*line.split(','))
        reward_character_properties[i.name] = i

    RewardMaiden = namedtuple('RewardMaiden',
        ['name', 'maiden_name',
         'my_maiden_flag', 'maiden_flag1', 'maiden_flag2'])
    for line in read_lines_nocomment(REWARD_MAIDEN_TABLE_FILENAME):
        i = RewardMaiden(*line.split(','))
        reward_maiden_properties[i.name] = i

    RewardCapsule = namedtuple('RewardCapsule',
        ['name', 'capsule_display_name',
         'capsule_index', 'sprite_index_after', 'capsule_flag'])
    for line in read_lines_nocomment(REWARD_CAPSULE_TABLE_FILENAME):
        i = RewardCapsule(*line.split(','))
        reward_capsule_properties[i.name] = i

    BANNED_FLAGS = [0x5F, 0x62]
    available_flags = list(reversed(range(0x20, 0x70)))
    for f in BANNED_FLAGS:
        available_flags.remove(f)

    done_locations = set()

    @staticmethod
    def get_properties_by_name(name):
        for properties in [OpenNPCGenerator.boss_properties,
                           OpenNPCGenerator.boss_location_properties,
                           OpenNPCGenerator.reward_item_properties,
                           OpenNPCGenerator.reward_character_properties,
                           OpenNPCGenerator.reward_maiden_properties]:
            if name in properties:
                return properties[name]

    @staticmethod
    def set_appropriate_item_icon(reward):
        item_index = int(reward.item_index, 0x10)
        if reward.item_icon_code == 'default':
            item = ItemObject.get(item_index)
            assert not item.sprite & 0x80
            if item.sprite & 0x40:
                sprite_class = 0x18
            else:
                sprite_class = 0x0a
            item_icon_code = '{0:0>2X}-{1:0>2x}'.format(
                sprite_class, item.sprite & 0x3F)
            reward = reward._replace(item_icon_code=item_icon_code)
        return reward

    @staticmethod
    def create_karlloon_elf_girl(parameters):
        MapEventObject.class_reseed('create_karlloon_elf_girl')

        def generate_item_remover_script(items):
            line_counter = 0
            lines = []
            for i in items:
                line = '{0:X}. 14(C2-{1:X}-0001-30-@{2:X}-FF)'.format(
                    line_counter, i, line_counter+3)
                line_counter += 1
                lines.append(line)
                opcode = '24' if i < 0x100 else '25'
                line = '{0:X}. {1}({2:X}-01)'.format(
                    line_counter, opcode, i & 0xFF)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 1C(@{1:X})'.format(line_counter, line_counter-2)
                line_counter += 1
                lines.append(line)
            line = '{0:X}. 1A(0A)'.format(line_counter)
            line_counter += 1
            lines.append(line)
            return '\n'.join(lines)

        consumables = sorted([i.index for i in ItemObject.every
                              if i.get_bit('usable_battle')])
        item_remover_script = generate_item_remover_script(consumables)
        equipment = sorted([i.index for i in ItemObject.every
                            if i.equipability and i.get_bit('equipable')])
        equipment_remover_script = generate_item_remover_script(equipment)

        def generate_party_offer_message(party_order, terminator='.'):
            if not terminator.endswith('<END MESSAGE>'):
                terminator = '{0}<END MESSAGE>'.format(terminator)
            character_names = {0: '$MAXIM$',
                               1: 'Selan',
                               2: 'Guy',
                               3: 'Artea',
                               4: 'Tia',
                               5: 'Dekar',
                               6: 'Lexis',
                               }
            line_counter = 0
            lines = []
            for i in party_order:
                character_name = character_names[i]
                line = '{0:X}. 6A({1:X}-@{2:X})'.format(
                    line_counter, i+1, line_counter+3)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 08: ...you leave {1}\nhere with me{2}'.format(
                    line_counter, character_name, terminator)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 1C(@REPLACE_ME)'.format(line_counter)
                line_counter += 1
                lines.append(line)
            line = '{0:X}. 08: ...you give me\na smile{1}'.format(
                line_counter, terminator)
            line_counter += 1
            lines.append(line)
            lines = [line.replace('REPLACE_ME', '{0:X}'.format(line_counter))
                     for line in lines]
            line = '{0:X}. 1A(0A)'.format(line_counter)  # effective no-op
            lines.append(line)
            line_counter += 1
            return '\n'.join(lines)

        shuffled_party = list(range(7))
        random.shuffle(shuffled_party)
        party_events = []
        for party_order in [shuffled_party, reversed(shuffled_party)]:
            line_counter = 0
            lines = []
            for i in party_order:
                line = '{0:X}. 6A({1:X}-@{2:X})'.format(
                    line_counter, i+1, line_counter+5)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 2C({1:X})'.format(line_counter, i)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 1B({1:X})'.format(line_counter, i+1)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 1E(0B-FF)'.format(line_counter)
                line_counter += 1
                lines.append(line)
                line = '{0:X}. 1C(@REPLACE_ME)'.format(line_counter)
                line_counter += 1
                lines.append(line)
            lines = [line.replace('REPLACE_ME', '{0:X}'.format(line_counter))
                     for line in lines]
            line = '{0:X}. 1A(0A)'.format(line_counter)  # effective no-op
            lines.append(line)
            line_counter += 1
            party_events.append('\n'.join(lines))

        barters = ['gold', 'consumables', 'equipment',
                   'party', 'reverse_party', 'capsules']

        first_offer = random.choice(barters)
        barters.remove(first_offer)
        if 'party' in barters and 'reverse_party' in barters:
            barters.remove('reverse_party')
        second_offer = random.sample(barters, 2)

        offer_messages = {
            'gold': '...you give me all\nof your gold',
            'consumables': '...you give me all of\nyour consumable items',
            'equipment': '...you give me all of\nyour spare equipment',
            'capsules': '...you give me all of\nyour capsule monsters',
            }

        def generate_offer_message(offer, terminator='.'):
            if not terminator.endswith('<END MESSAGE>'):
                terminator = '{0}<END MESSAGE>'.format(terminator)
            if offer in offer_messages:
                message = '0000. 08: {0}{1}'.format(
                    offer_messages[offer], terminator)
                return message

            if offer == 'reverse_party':
                party_order = list(reversed(shuffled_party))
            else:
                assert offer == 'party'
                party_order = list(shuffled_party)
            return generate_party_offer_message(party_order, terminator)

        capsule_flags = [c.capsule_flag for c in
                         OpenNPCGenerator.reward_capsule_properties.values()]
        capsule_remover_script = '0000. 81(FF)\n'
        for i, cf in enumerate(sorted(capsule_flags)):
            capsule_remover_script += '000{0}. 1B({1})\n'.format(i+1, cf)

        offer_acceptance_events = {
            'gold': '0000. 22(0)',
            'capsules': capsule_remover_script,
            'consumables': item_remover_script,
            'equipment': equipment_remover_script,
            'party': party_events[0],
            'reverse_party': party_events[1],
            }

        karl_first_offer = MapEventObject.Script.shift_line_numbers(
            generate_offer_message(first_offer), 0x1000)
        a = generate_offer_message(second_offer[0], terminator=', and...')
        b = generate_offer_message(second_offer[1], terminator='.')
        a = MapEventObject.Script.shift_line_numbers(a, 0x3000)
        b = MapEventObject.Script.shift_line_numbers(b, 0x3400)
        karl_second_offer = '\n'.join([a, b])

        karl_first_offer_accept = MapEventObject.Script.shift_line_numbers(
            offer_acceptance_events[first_offer], 0x2000)
        a = MapEventObject.Script.shift_line_numbers(
            offer_acceptance_events[second_offer[0]], 0x4000)
        b = MapEventObject.Script.shift_line_numbers(
            offer_acceptance_events[second_offer[1]], 0x4600)
        karl_second_offer_accept = '\n'.join([a, b])

        parameters['karl_first_offer'] = karl_first_offer
        parameters['karl_second_offer'] = karl_second_offer
        parameters['karl_first_offer_accept'] = karl_first_offer_accept
        parameters['karl_second_offer_accept'] = karl_second_offer_accept
        patch_with_template('karlloon_elf_girl', parameters)

    @staticmethod
    def create_egg_girl(parameters):
        MapEventObject.class_reseed('create_egg_girl')
        loop_template = ('{0:0>4X}. 14(C0-002B-{1:0>4X}-30-@{2:0>4X}-FF)\n'
                         '{3:0>4X}. 1C(@{4:0>4X})\n')
        s = ''
        for i in range(0, 99):
            address = 0x2000 + (i*0x20)
            character = random.randint(0, 6)
            character_address = 0x6000 + (0x100 * character)
            s += loop_template.format(address, i, address+0x20, address+0x10,
                                      character_address)
        s += '{0:0>4X}. 1A(0A)\n'.format(address+0x20)
        parameters['egg_girl_event'] = s
        patch_with_template('egg_girl', parameters)

    @staticmethod
    def create_hint_shop(blue_chests, wild_jelly_map,
                         iris_iris, thieves):
        IRIS_ITEMS = sorted(range(0x19c, 0x1a6))
        MapEventObject.class_reseed('create_hint_shop')
        boss_events = []
        blue_chests = [b for b in blue_chests if b.item.index in IRIS_ITEMS]
        num_hints = 50
        hints_by_treasure = {}
        hints = []
        while True:
            num_temp = 11
            temp = generate_hints(boss_events, blue_chests, wild_jelly_map,
                                  iris_iris, thieves, num_hints=num_temp)
            for hint in temp:
                for item_index in IRIS_ITEMS:
                    item = ItemObject.get(item_index)
                    s = hint.replace('\n', ' ')
                    if item.name in s:
                        key = item.name
                        break
                    elif 'Master Jelly' in s:
                        key = 'jelly'
                        break
                else:
                    key = 'other'
                if key not in hints_by_treasure:
                    hints_by_treasure[key] = []
                if hint not in hints_by_treasure[key]:
                    hints_by_treasure[key].append(hint)
                if hint not in hints:
                    hints.append(hint)
            if len(hints) >= num_hints*2:
                break

        hints = []
        unique_keys = sorted(hints_by_treasure.keys())
        keys = []
        while len(hints) < num_hints:
            candidates = [k for k in unique_keys if k not in keys]
            if not candidates:
                candidates = [k for k in unique_keys if k not in keys[-5:]]
            key = random.choice(candidates)
            keys.append(key)
            candidates = [h for h in hints_by_treasure[key] if h not in hints]
            if not candidates:
                continue
            hints.append(candidates[0])

        hint_variable = 0x0d
        temp_flag = 0xf0
        hints = hints[:num_hints]
        hints_script = []
        line_number = 0x2000
        for i, hint in enumerate(reversed(hints)):
            hint_number = num_hints - i
            line = '{0:0>4X}. 14(12-{1:0>2X}-{2:0>2X}-30-@{3:X}-FF)'
            jump_line_number = line_number + 3
            line = line.format(line_number, hint_variable,
                               hint_number, jump_line_number)
            hints_script.append(line)
            line_number += 1
            hint = '{0}. {1}'.format(hint_number, hint)
            line = '{0:0>4X}. 9E: <POSITION 01>{1}<END MESSAGE>'.format(
                line_number, hint)
            hints_script.append(line)
            line_number += 1
            line = '{0:0>4X}. 15({1:0>2X}-@6800)'.format(line_number,
                                                         temp_flag)
            hints_script.append(line)
            line_number += 1
        hints_script.append('{0:0>4X}. 1A(0A)'.format(line_number))
        hints_script = '\n'.join(hints_script)

        map_index = 0x69
        hint_shop_npc_index = MapMetaObject.get(map_index).get_next_npc_index()
        hint_shop_map_npc_index = hint_shop_npc_index + 0x4f

        script = MapEventObject.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(map_index))
        min_line = script.script[0][0]
        sprite = 0x37
        new_command = (min_line-1, 0x68, [hint_shop_map_npc_index, sprite])
        script.script.insert(0, new_command)
        script.realign_addresses()

        hint_shop_signature = '{0:0>2X}-C-{1:0>2X}'.format(
            map_index, hint_shop_map_npc_index)
        hint_shop_location = '69:06,04'
        parameters = {
            'hint_shop_npc_index': hint_shop_npc_index,
            'hint_shop_signature': hint_shop_signature,
            'hint_shop_location': hint_shop_location,
            'temp_flag': temp_flag,
            'hint_variable': hint_variable,
            'max_num_hints': num_hints + 1,
            'hints_script': hints_script,
        }
        patch_with_template('hint_shop', parameters)

    @staticmethod
    def create_priest(location):
        map_index, coords = location.split(':')
        x, y = coords.split(',')
        map_index = int(map_index, 0x10)
        x, y = int(x, 0x10), int(y, 0x10)
        script = MapEventObject.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(map_index))
        min_line = script.script[0][0]
        map_meta = MapMetaObject.get(map_index)
        npc_index = map_meta.get_next_npc_index()
        map_npc_index = npc_index + 0x4f
        sprite = 0x32
        new_command = (min_line-1, 0x68, [map_npc_index, sprite])
        script.script.insert(0, new_command)
        script.realign_addresses()

        priest_script = ('!npc {0:0>2x} (05) {1}\n'
                         'EVENT {2:0>2X}-C-{3:0>2X}\n'
                         '0000. 19()\n'
                         '0001. 00()\n').format(npc_index, location,
                                                map_index, map_npc_index)
        patch_game_script(priest_script, warn_double_import=False)

    @staticmethod
    def create_crown(location):
        location = OpenNPCGenerator.boss_location_properties[location]
        map_index = location.map_index
        x = location.npc_x
        y = location.npc_y
        location = '{0}:{1},{2}'.format(map_index, x, y)
        map_index = int(map_index, 0x10)
        script = MapEventObject.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(map_index))
        min_line = script.script[0][0]
        map_meta = MapMetaObject.get(map_index)
        npc_index = map_meta.get_next_npc_index()
        map_npc_index = npc_index + 0x4f
        sprite = 0x48
        new_command = (min_line-1, 0x68, [map_npc_index, sprite])
        script.script.insert(0, new_command)
        script.realign_addresses()

        crown_script = ('!npc {0:0>2x} (05) {1}\n'
                        'EVENT {2:0>2X}-C-{3:0>2X}\n'
                        '0000. 00()\n').format(npc_index, location,
                                               map_index, map_npc_index)
        patch_game_script(crown_script, warn_double_import=False)

    @staticmethod
    def create_prince(location):
        event_flag = OpenNPCGenerator.available_flags.pop()
        location = OpenNPCGenerator.boss_location_properties[location]
        map_bgm = location.map_bgm
        map_index = location.map_index
        x = location.npc_x
        y = location.npc_y
        location = '{0}:{1},{2}'.format(map_index, x, y)
        map_index = int(map_index, 0x10)
        script = MapEventObject.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(map_index))
        min_line = script.script[0][0]
        map_meta = MapMetaObject.get(map_index)
        npc_index = map_meta.get_next_npc_index()
        map_npc_index = npc_index + 0x4f
        sprite = 0x14
        new_command = (min_line-1, 0x68, [map_npc_index, sprite])
        script.script.insert(0, new_command)
        addr = MapEventObject.Script.Address(min_line, is_local=True)
        new_command = (min_line-2, 0x15, [event_flag, addr])
        script.script.insert(0, new_command)
        script.realign_addresses()

        parameters = {'event_flag': event_flag,
                      'location': location,
                      'map_bgm': map_bgm,
                      'map_index': map_index,
                      'map_npc_index': map_npc_index,
                      'npc_index': npc_index,
                      }
        patch_with_template('prince', parameters)

    @staticmethod
    def create_boss_npc(location, boss, reward1=None, reward2=None,
                        parameters=None):
        OpenNPCGenerator.done_locations.add(location)
        if parameters is not None:
            parameters = dict(parameters)
        else:
            parameters = {}
        if not (reward1 and reward2):
            reward1 = reward1 or reward2
            reward2 = None
        parameters['reward1_event'] = ''
        parameters['reward2_event'] = ''
        parameters['boss_flag'] = OpenNPCGenerator.available_flags.pop()

        location = OpenNPCGenerator.boss_location_properties[location]

        if isinstance(boss, str):
            boss = OpenNPCGenerator.boss_properties[boss]
        else:
            assert isinstance(boss, BossFormationObject)
            index = boss.index
            if boss.monster_indexes == boss.old_data['monster_indexes']:
                bosses = [b for b in OpenNPCGenerator.boss_properties.values()
                          if int(b.boss_formation_index, 0x10) == index]
                assert len(bosses) == 1
                boss = bosses[0]
            else:
                name = 'f{0:0>2X}'.format(index)
                sprite_index_before = boss.guess_sprite()
                battle_bgm = boss.guess_bgm()
                boss = OpenNPCGenerator.Boss(
                    name, sprite_index_before, index, battle_bgm)


        old_event_signature = '%s-X-XX' % location.map_index
        map_index = int(location.map_index, 0x10)
        npc_index = MapMetaObject.get(map_index).get_next_npc_index()
        parameters['npc_index'] = npc_index
        parameters['npc_event_index'] = npc_index + 0x4f

        meo = MapEventObject.get(map_index)
        el = meo.get_eventlist_by_index('X')
        script = el.get_script_by_index(None)

        old_event_text = '#' + str(script)
        assert old_event_text.startswith('#EVENT')
        addrs = [int(addr, 0x10) for addr in
                 MapEventObject.Script.LINE_MATCHER.findall(old_event_text)]
        min_addr, max_addr = min(addrs), max(addrs)
        shift_amount = 0x1000 + max_addr

        old_event_text = MapEventObject.Script.shift_line_numbers(
            old_event_text, shift_amount)
        parameters['old_event_start'] = shift_amount + min_addr
        parameters['old_event'] = old_event_text

        for i in range(1, 3):
            reward = None
            if i == 1:
                reward = reward1
            if i == 2:
                reward = reward2

            if reward in OpenNPCGenerator.reward_item_properties:
                reward = OpenNPCGenerator.reward_item_properties[reward]
                event_text = OpenNPCGenerator.REWARD_EVENT_ITEM.replace(
                    '{{reward_id}}', str(i))
                if i == 2:
                    event_text = MapEventObject.Script.shift_line_numbers(
                        event_text, 0x2000)
                assert not parameters['reward%s_event' % i]
                parameters['reward%s_event' % i] = event_text
                item_index = int(reward.item_index, 0x10)
                item_acquire_opcode = '21' if item_index >= 0x100 else '20'
                item_acquire_opcode = '{0}({1:0>2X}-01)'.format(
                        item_acquire_opcode, item_index & 0xFF)
                parameters['item_acquire_opcode'] = item_acquire_opcode
                parameters['sprite_index_middle'] = '48'
                parameters['sprite_index_after'] = '48'
                parameters['after_event'] = ''
                parameters['after_event_start'] = '7FFF'
                reward = OpenNPCGenerator.set_appropriate_item_icon(reward)

            elif reward in OpenNPCGenerator.reward_character_properties:
                reward = OpenNPCGenerator.reward_character_properties[reward]
                event_text = OpenNPCGenerator.REWARD_EVENT_CHARACTER
                if 'after_event' in parameters:
                    assert not parameters['after_event']
                parameters['after_event'] = event_text
                parameters['sprite_index_after'] = reward.character_index
                character_flag = int(reward.character_index, 0x10) + 1
                parameters['character_flag'] = character_flag
                parameters['after_event_start'] = '6000'

            elif reward in OpenNPCGenerator.reward_maiden_properties:
                reward = OpenNPCGenerator.reward_maiden_properties[reward]
                event_text = OpenNPCGenerator.REWARD_EVENT_MAIDEN
                if i == 2:
                    event_text = MapEventObject.Script.shift_line_numbers(
                        event_text, 0x2000)
                parameters['reward%s_event' % i] = event_text
                parameters['sprite_index_after'] = '44'
                parameters['after_event'] = ''
                parameters['after_event_start'] = '7FFF'

            elif reward in OpenNPCGenerator.reward_capsule_properties:
                reward = OpenNPCGenerator.reward_capsule_properties[reward]
                event_text = OpenNPCGenerator.REWARD_EVENT_CAPSULE
                if 'after_event' in parameters:
                    assert not parameters['after_event']
                parameters['after_event'] = event_text
                parameters['after_event_start'] = '6000'

            elif reward is not None:
                print('ERROR: Unable to process reward "%s".' % reward)
                return

            if reward is not None:
                for attr in reward._fields:
                    if attr == 'name':
                        continue
                    parameters[attr] = getattr(reward, attr)

            if i == 1:
                reward1_tuple = reward
            if i == 2:
                reward2_tuple = reward

            for attr in sorted(parameters.keys()):
                if 'item' in attr:
                    otherattr = attr.replace('item', 'item%s' % i)
                    parameters[otherattr] = parameters[attr]

        for propobj in (boss, location):
            for attr in propobj._fields:
                if attr == 'name':
                    continue
                assert attr not in parameters
                parameters[attr] = getattr(propobj, attr)

        if 'victory' in (reward1, reward2):
            patch_with_template('final_boss_npc', parameters)
        elif reward1 and reward2:
            patch_with_template('boss_npc_double_reward', parameters)
        else:
            parameters['reward_event'] = parameters['reward1_event']
            patch_with_template('boss_npc', parameters)

        npc_event_index = int(parameters['npc_event_index'], 0x10)
        signature = '{0:0>2X}-C-{1:0>2X}'.format(map_index, npc_event_index)
        return location, boss, reward1_tuple, reward2_tuple, signature


def set_new_leader_for_events(new_character_index, old_character_index=0):
    EXEMPT_EVENTS = {'02-B-01', '04-B-02', '1C-B-03', '2C-B-04',
                     '45-B-02', '7A-B-01', 'A6-B-03', '02-B-02'}
    command_replace_dict = {
        0x33: [1],
        0x86: [0],
        0x8c: [0],
    }
    for meo in MapEventObject.every:
        for el in meo.event_lists:
            for script in el.scripts:
                if script.signature in EXEMPT_EVENTS:
                    continue
                new_script = []
                for line_number, opcode, parameters in script.script:
                    if opcode in command_replace_dict:
                        replace_args = command_replace_dict[opcode]
                        for arg in replace_args:
                            if parameters[arg] == old_character_index:
                                parameters[arg] = new_character_index
                    new_script.append((line_number, opcode, parameters))
                script.script = new_script


def make_wild_jelly(jelly_flag):
    MapEventObject.class_reseed('make_wild_jelly')
    JELLY_SPRITE_INDEX = 0x94
    JELLY_FORMATIONS = [0x03, 0x07, 0x13]
    jelly_formation = FormationObject.get(random.choice(JELLY_FORMATIONS))
    assert 'Jelly' in str(jelly_formation)
    while True:
        meo = random.choice(MapEventObject.every)
        npcs = PLAINTEXT_NPC_MATCHER.findall(str(meo))
        candidates = []
        for (index, misc, x, y, event, sprite, formation) in npcs:
            if (event or not formation or int(misc, 0x10) != 0
                    or int(index, 0x10) < 0):
                continue
            if '<=' not in x or '<=' not in y:
                continue
            if int(sprite, 0x10) == JELLY_SPRITE_INDEX:
                continue
            candidates.append((index, x, y))
        if len(candidates) < 2:
            continue
        break
    index, x, y = random.choice(candidates)
    index = int(index, 0x10)
    map_npc_index = 0x4f + index
    script = meo.event_lists[0].scripts[0]
    assert '{0:0>2X}-X-XX'.format(meo.index) in str(script)
    new_script = []
    for (l, o, p) in script.script:
        if o == 0x7B and p[0] == map_npc_index:
            new_script.append((l, 0x1A, [0x0A]))
        else:
            new_script.append((l, o, p))
    min_line = min(l for (l, o, p) in new_script)
    new_script.insert(0, (min_line-1, 0x7B,
                          [map_npc_index, JELLY_SPRITE_INDEX]))
    script.script = new_script
    script.realign_addresses()

    mfo = MapFormationsObject.get(meo.index)
    assert index > 0
    mfo.formation_indexes[index-1] = jelly_formation.index
    min_x, x, max_x = x.split('<=')
    min_y, y, max_y = y.split('<=')
    min_x, max_x, min_y, max_y = [int(c, 0x10)
                                  for c in (min_x, max_x, min_y, max_y)]
    min_x, min_y = min_x-2, min_y-2
    max_x, max_y = max_x+2, max_y+2
    width = max_x - min_x
    height = max_y - min_y
    s = str(meo)
    for tile_index in range(0x1F, -1, -1):
        if '# TILE {0:0>2X}'.format(tile_index) in s:
            continue
        break
    else:
        raise Exception('No space for additional tiles.')

    words = ['incredible', 'absurd', 'preposterous', 'unbelievable',
             'inconceivable', 'impossible', 'ridiculous', 'bakana']
    word = random.choice(sorted(words))
    jelly_dialogue = '{0}-{1}'.format(word[0].upper(), word.lower())
    min_x = max(0, min_x)
    min_y = max(0, min_y)
    width = min(width, 0xFF-min_x)
    height = min(height, 0xFF-min_y)
    parameters = {
        'map_index': meo.index,
        'npc_index': map_npc_index,
        'tile_index': tile_index,
        'x': min_x,
        'y': min_y,
        'width': str(width),
        'height': str(height),
        'jelly_flag': jelly_flag,
        'jelly_dialogue': jelly_dialogue,
        'map_bgm': 0x07,
        }
    patch_with_template('boss_jelly', parameters)
    return meo.index


def assign_iris_shop(iris_item):
    MapEventObject.class_reseed('assign_iris_shop')
    item_types = {
        'sword': 'weapon',
        'shield': 'armor',
        'helmet': 'armor',
        'armor': 'armor',
        'ring': 'armor',
        'jewel': 'armor',
        'staff': 'weapon',
        'pot': 'item',
        'tiara': 'armor',
        }
    keys = [k for k in item_types
            if k in ItemObject.get(iris_item).name.lower()]
    assert len(keys) == 1
    shop_type = item_types[keys[0]]
    candidates = [s for s in ShopObject.every
                  if s.zone_name not in ('NONE', 'VARIOUS')
                  and len(s.wares[shop_type]) > 0]
    assert candidates
    shop = random.choice(candidates)
    replace_item = random.choice(shop.wares[shop_type])
    shop.wares[shop_type].remove(replace_item)
    shop.wares[shop_type] = [iris_item] + shop.wares[shop_type]

    prices = sorted([i.price for i in ItemObject.every if i.price > 0])
    max_index = len(prices) - 1
    index = random.randint(random.randint(0, max_index), max_index)
    ItemObject.get(iris_item).price = prices[index]

    return shop.index


def generate_hints(boss_events, blue_chests, wild_jelly_map,
                   iris_iris, thieves, num_hints=500):
    BG_OVERRIDES = {
        0xee: [0x0e, 0x0f],
        0xef: [0x0e, 0x0f],
        }

    iris_shop_item, iris_shop = iris_iris
    iris_shop = ShopObject.get(iris_shop)

    boss_matcher = re.compile('\. 53\((..)\) ')
    bg_matcher = re.compile('\. 74\((..)\) ')
    formation_matcher = re.compile('#.*\(FORMATION (..): ')
    chest_matcher = re.compile('# CHEST (..): ')
    getitem_matcher = re.compile('\. 2([01])\((..)-01\) ')
    character_matcher = re.compile('\. 2B\((..)\) ')
    capsule_matcher = re.compile('\. 81\((..)\) ')
    maiden_matcher = re.compile('My name is (\S*)\.')

    blue_chests = [b for b in blue_chests
                   if 'dragon egg' not in b.item.name.lower()]
    hint_topics = ((boss_events * 4) + blue_chests
                   + [wild_jelly_map, iris_shop] + list(thieves))
    messages = []
    for _ in range(num_hints):
        hint_topic = random.choice(hint_topics)
        hint_target = None
        event_boss = None
        map_index = None
        if hint_topic in boss_events:
            map_index, _, _ = hint_topic.split('-')
            map_index = int(map_index, 0x10)
            script = MapEventObject.get_script_by_signature(hint_topic).pretty
            event_boss = boss_matcher.findall(script)
            assert len(event_boss) == 1
            event_boss = BossFormationObject.get(int(event_boss[0], 0x10))
            event_boss = event_boss.boss.name
            items = getitem_matcher.findall(script)
            items = [''.join((x, y)) for (x, y) in items]
            items = [ItemObject.get(int(i, 0x10)).name for i in items]
            characters = character_matcher.findall(script)
            characters = [CharacterObject.get(int(c, 0x10)).name
                          for c in characters]
            capsules = capsule_matcher.findall(script)
            capsules = [int(c, 0x10) for c in capsules]
            capsules = sorted([
                c.capsule_display_name
                for c in OpenNPCGenerator.reward_capsule_properties.values()
                if int(c.capsule_index, 0x10) in capsules])
            maidens = maiden_matcher.findall(script)
            hint_targets = (items + characters + capsules + maidens)
            hint_targets = (hint_targets * 2) + [event_boss]
            hint_target = random.choice(hint_targets)
            if hint_target in items:
                hint_target = 'The {0}'.format(hint_target)
            elif hint_target in capsules:
                assert hint_target[0] == '{'
                if hint_target[1] in 'AEIOU':
                    hint_target = 'An {0}'.format(hint_target)
                else:
                    hint_target = 'A {0}'.format(hint_target)

        elif hint_topic in blue_chests:
            map_index = hint_topic.map_index
            if 'dragon egg' in hint_topic.item.name.lower():
                hint_target = 'A dragon egg'
            else:
                hint_target = 'The {0}'.format(hint_topic.item.name)

        elif hint_topic is iris_shop:
            map_index = None
            hint_target = 'The {0}'.format(ItemObject.get(iris_shop_item).name)

        elif hint_topic in thieves:
            map_index, _, _ = hint_topic.split('-')
            map_index = int(map_index, 0x10)

        else:
            assert hint_topic == wild_jelly_map
            map_index = wild_jelly_map
            hint_target = "The Master Jelly"

        if hint_target == 'Maxim':
            hint_target = '$MAXIM$'

        hint_type = None
        if hint_topic not in thieves and hint_topic != iris_shop:
            meo = MapEventObject.get(map_index)
            zone_maps = meo.neighbors
            old_zone_text = '\n\n'.join([m.old_pretty for m in zone_maps])
            if hint_topic in boss_events:
                new_zone_text = MapEventObject.get_script_by_signature(
                    hint_topic).pretty
            else:
                new_zone_text = ''
            if map_index in BG_OVERRIDES:
                bgs = BG_OVERRIDES[map_index]
            else:
                bgs = bg_matcher.findall(old_zone_text)
            formations = formation_matcher.findall(old_zone_text)
            monsters = [m for f in formations
                        for m in FormationObject.get(int(f, 0x10)).monsters]
            monsters = [m for m in monsters if m is not None]
            chests = chest_matcher.findall(old_zone_text)
            chest_items = [ChestObject.get(int(c, 0x10)).old_item
                           for c in chests]
            chest_items = [i for i in chest_items if i.rank > 0]
            bosses = boss_matcher.findall(new_zone_text)
            bosses = [BossFormationObject.get(int(b, 0x10)) for b in bosses]
            assert len(bosses) < 2

            candidates = []
            if bgs:
                candidates.append('bg')
            if monsters:
                candidates.append('monsters')
            else:
                candidates.append(None)
            if chests:
                candidates.append('chests')
            candidates = candidates * 2
            if bosses and hint_target != event_boss:
                candidates.append('bosses')
            hint_type = random.choice(candidates)

        location_hint = None
        if isinstance(hint_topic, ShopObject):
            location_hint = 'in a shop in {0}'.format(iris_shop.zone_name)
        elif hint_type == 'bg':
            bg_hints = {
                0x01: 'in or near a mountain',
                0x02: 'in a tower',
                0x04: 'in a grassy area',
                0x05: 'in a shrine',
                0x07: 'in or near a mountain',
                0x08: 'in the sky',
                0x09: 'in a dungeon',
                0x0a: 'in a tower',
                0x0b: 'in or near a cave',
                0x0c: 'in or near a cave',
                0x0d: 'in or near a cave',
                0x0e: 'in a wet place',
                0x0f: 'in a wet place',
                0x10: 'in or near a cave',
                0x11: 'in or near a cave',
                0x12: 'in a hot place',
                0x13: 'in a hot place',
                0x14: 'in a hot place',
                0x15: 'in a tower',
                0x16: 'in a dungeon',
                }
            bg = random.choice(bgs)
            if isinstance(bg, str):
                bg = int(bg, 0x10)
            if bg not in bg_hints:
                location_hint = 'somewhere strange'
            else:
                location_hint = bg_hints[bg]

        elif hint_type == 'monsters':
            m = random.choice(monsters)
            name = m.name
            if name[-1] in 'sxz' or name.endswith('sh') or name.endswith('ch'):
                name += 'e'
            if name[-1] == 'y':
                name = name[:-1] + 'ie'
            if 'monstermash' in get_activated_codes():
                location_hint = 'in a place where {0}s may dwell'.format(name)
            else:
                location_hint = 'in a place where {0}s dwell'.format(name)

        elif hint_type == 'chests':
            c = random.choice(chest_items)
            word = c.name
            if word[0].lower() in 'aeiou':
                word = 'an {0}'.format(word)
            else:
                word = 'a {0}'.format(word)
            location_hint = 'in a place where you might find {0} in a chest'
            location_hint = location_hint.format(word)

        elif hint_type == 'bosses':
            assert len(bosses) == 1
            b = bosses[0]
            location_hint = 'guarded by {0}'.format(b.boss.name)

        elif hint_type is None:
            location_hint = 'in a secluded location'

        else:
            location_hint = 'somewhere strange'

        if hint_topic in thieves:
            zone_name = MapEventObject.get(map_index).zone_name
            hint = 'I saw a thief with rare treasure in {0}.'.format(zone_name)
        else:
            hint = '{0} is {1}.'.format(hint_target, location_hint)
        MINIMUM_LINE_LENGTH = 10
        target_line_length = len(hint) / 4
        target_line_length = max(target_line_length, MINIMUM_LINE_LENGTH)
        message = ''
        for word in hint.split(' '):
            message = '{0} {1}'.format(message, word).lstrip()
            message = message.replace('\n ', '\n')
            prev_line_length = len(message.split('\n')[-1])
            if prev_line_length > target_line_length:
                message += '\n'
        message = message.strip()
        assert message.count('\n') <= 3
        messages.append(message)

    return messages


def generate_hint_npcs(boss_events, blue_chests, wild_jelly_map,
                       iris_iris, thieves):
    MapEventObject.class_reseed('generate_hints')
    hint_npcs = []
    for meo in MapEventObject.every:
        npcs = PLAINTEXT_NPC_MATCHER.findall(str(meo))
        for (index, misc, x, y, event, sprite, formation) in npcs:
            if formation or '-C-' not in event or int(misc, 0x10) != 0:
                continue
            if '<=' not in x or '<=' not in y:
                continue
            script = MapEventObject.get_script_by_signature(event)
            opcodes = {o for (l, o, p) in script.script}
            if 8 in opcodes and opcodes <= {0, 8} and event in meo.old_pretty:
                hint_npcs.append(event)

    num_hints = len(hint_npcs)
    hints = generate_hints(boss_events, blue_chests, wild_jelly_map,
                           iris_iris, thieves, num_hints=num_hints)

    assert len(hints) == len(hint_npcs)
    for npc, hint in zip(hint_npcs, hints):
        npc_script = ('EVENT {0}\n'
                      '0000. 08: {1}<END EVENT>').format(npc, hint)
        patch_game_script(npc_script, warn_double_import=False)


def generate_thieves(iris_item):
    MapEventObject.class_reseed('generate_thieves')
    candidates = []
    for meo in MapEventObject.every:
        npcs = PLAINTEXT_NPC_MATCHER.findall(str(meo))
        for (index, misc, x, y, event, sprite, formation) in npcs:
            if formation or '-C-' not in event or int(misc, 0x10) != 0:
                continue
            if '<=' not in x or '<=' not in y:
                continue
            script = MapEventObject.get_script_by_signature(event)
            opcodes = {o for (l, o, p) in script.script}
            if 8 in opcodes and opcodes <= {0, 8} and event in meo.old_pretty:
                candidates.append(event)

    buyable_items = {i for s in ShopObject.every for i in s.wares_flat}
    rare_items = [i for i in ItemObject.every
                  if i.price > 0 and i.rank > 0 and i not in buyable_items]
    rare_items = sorted(rare_items, key=lambda i: i.rank)
    max_index = len(rare_items)-1
    index = random.randint(random.randint(1, max_index), max_index)
    iris_exchange_item = rare_items[index]
    iris_exchange_quantity = 1
    while random.choice([True, False]):
        iris_exchange_quantity += 1
    iris_exchange_quantity = min(iris_exchange_quantity, 99)

    buyable_items = sorted(buyable_items, key=lambda i: i.price)
    max_index = len(buyable_items)-1
    index = random.randint(random.randint(1, max_index), max_index)
    second_exchange_item = buyable_items[index]
    second_exchange_quantity = 1
    while True:
        if (second_exchange_item.rank * second_exchange_quantity
                > iris_exchange_item.rank):
            break
        second_exchange_quantity += 1
    while random.choice([True, False]):
        second_exchange_quantity += 1
    second_exchange_quantity = min(second_exchange_quantity, 99)

    def get_add_item_command(item_index, quantity):
        return '{0:0>2X}({1:0>2X}-{2:0>2X})'.format(
            0x20 + (item_index >> 8), item_index & 0xFF, quantity)

    def get_remove_item_command(item_index, quantity):
        return '{0:0>2X}({1:0>2X}-{2:0>2X})'.format(
            0x24 + (item_index >> 8), item_index & 0xFF, quantity)

    thief1, thief2 = random.sample(candidates, 2)
    map_index, _, map_event_index = thief1.split('-')

    trade_quantity_item = '{0}x {1}'.format(iris_exchange_quantity,
                                            iris_exchange_item.name)
    parameters = {
        'signature': thief1,
        'iris_item_index': '{0:0>4X}'.format(iris_item),
        'iris_item_name': ItemObject.get(iris_item).name,
        'trade_quantity_item': trade_quantity_item.rstrip('.'),
        'trade_item_index': '{0:0>4X}'.format(iris_exchange_item.index),
        'quantity': iris_exchange_quantity,
        'add_item_command': get_add_item_command(iris_item, 1),
        'remove_item_command': get_remove_item_command(
            iris_exchange_item.index, iris_exchange_quantity),
        }
    patch_with_template('thief1', parameters)

    trade_quantity_item = '{0}x {1}'.format(second_exchange_quantity,
                                            second_exchange_item.name)
    if trade_quantity_item.endswith('.'):
        trade_quantity_item = trade_quantity_items[:-1]
    parameters = {
        'signature': thief2,
        'exchange_item_name': iris_exchange_item.name.rstrip('.'),
        'trade_quantity_item': trade_quantity_item,
        'trade_item_index': '{0:0>4X}'.format(second_exchange_item.index),
        'quantity': second_exchange_quantity,
        'add_item_command': get_add_item_command(iris_exchange_item.index, 1),
        'remove_item_command': get_remove_item_command(
            second_exchange_item.index, second_exchange_quantity),
        }
    patch_with_template('thief2', parameters)

    sprites = [0x39, 0x3a]
    random.shuffle(sprites)
    for (signature, sprite) in zip([thief1, thief2], sprites):
        map_index, _, map_event_index = signature.split('-')
        map_index = int(map_index, 0x10)
        map_event_index = int(map_event_index, 0x10)
        script = MapEventObject.get_script_by_signature(
            '{0:0>2X}-X-XX'.format(map_index))
        new_script = []
        for l, o, p in script.script:
            if o == 0x68 and p[0] == map_event_index:
                p = [map_event_index, sprite]
            new_script.append((l, o, p))
        script.script = new_script

    return (thief1, thief2)


def apply_iris_wards(maps, wild_jelly_map):
    IRIS_ITEMS = sorted(range(0x19c, 0x1a6))
    VARIABLE = 0x05
    for meo in maps:
        map_index = meo.index
        signature = '{0:0>2X}-X-XX'.format(map_index)
        script = meo.get_script_by_signature(signature)
        seen_addresses = set()
        for (l, o, p) in script.script:
            for pp in p:
                if isinstance(pp, MapEventObject.Script.Address):
                    seen_addresses.add(pp.address)

        monster_loaders = []
        for (l, o, p) in script.script:
            if l in seen_addresses:
                continue
            if o == 0x7B:
                if map_index == wild_jelly_map and 0x94 in p:
                    continue
                monster_loaders.append((l, o, p))

        for i in [0, 1]:
            signature = '{0:0>2X}-A-{1:0>2X}'.format(map_index, i)
            script = meo.get_script_by_signature(signature)
            if script is None or script.script == [(0, 0, [])]:
                break
        else:
            print('WARNING: No event for ward {0:0>2X}.'.format(map_index))
            continue

        s = 'EVENT {0}\n0000. 1D({1:0>2X}-00)\n'.format(signature, VARIABLE)
        line_number = 1
        for item_index in IRIS_ITEMS:
            if item_index == IRIS_ITEMS[-1]:
                jump_to = 0x100
            else:
                jump_to = line_number+2
            line = '{0:0>4X}. 14(C2-{1:0>4X}-0001-30-@{2:X}-FF)\n'
            s += line.format(line_number, item_index, jump_to)
            line_number += 1
            s += '{0:0>4X}. 1E({1:0>2X}-01)\n'.format(line_number, VARIABLE)
            line_number += 1

        num_monsters = len(monster_loaders)
        thresholds = []
        while len(thresholds) < num_monsters:
            to_sample = min(num_monsters-len(thresholds), 9)
            thresholds += random.sample(list(range(1, 10)), to_sample)
        thresholds = sorted(thresholds)
        assert len(thresholds) == num_monsters

        line_number = 0x100
        random.shuffle(monster_loaders)
        for threshold, (l, o, p) in zip(thresholds, monster_loaders):
            if (l, o, p) == monster_loaders[-1]:
                jump_to = 0x7FFF
            else:
                jump_to = line_number+2
            line = '{0:0>4X}. 14(12-{1:0>2X}-{2:0>2X}-30-@{3:X}-FF)\n'
            s += line.format(line_number, VARIABLE, threshold, jump_to)
            line_number += 1
            s += '{0:0>4X}. 2E({1:0>2X})\n'.format(line_number, p[0])
            line_number += 1
        s += '7FFF. 00()'
        patch_game_script(s, warn_double_import=False)


def read_credits():
    f = get_open_file(get_outfile())
    f.seek(addresses.credits)
    s = ''
    lines = []
    while True:
        line = ''
        while True:
            peek = ord(f.read(1))
            if peek == 2:
                double_peek = ord(f.read(1))
                line += '\n' * double_peek
            elif peek == 1:
                line += '->'
                break
            elif peek == 4:
                line += hexify(b'\x04' + f.read(9))
                break
            elif peek == 5:
                line += '<-'
                break
            else:
                raise Exception('Unknown credits opcode')
        while True:
            if peek == 4:
                break
            c = f.read(1)
            if ord(c) == 0:
                break
            line += c.decode('ascii')
        lines.append(line)
        if peek == 4:
            break
    lines = [l2 for l in lines for l2 in l.split('\n')]
    new_lines = []
    for line in lines:
        if line.startswith('<-'):
            line = line[2:].strip()
        elif line.startswith('->'):
            line = '{0:>28}'.format(line[2:])
        new_lines.append(line)
    return '\n'.join(new_lines)


def write_credits(boss_events, blue_chests, wild_jelly_map,
                  iris_iris, thieves):
    iris_shop_item, iris_shop = iris_iris
    iris_shop = ShopObject.get(iris_shop)

    def center(line):
        assert len(line) <= 28
        line = '{0:^28}'.format(line)
        return line.rstrip()

    def right_justify(line):
        assert len(line) <= 28
        line = '{0:>28}'.format(line)
        return line

    def num_to_text(value):
        digits = 'pqrstvwxyz'
        s = ''
        for c in str(value):
            s += digits[int(c)]
        return s.lower()

    s1 = ''
    s1 += center('Abyssonym Presents')
    s1 += '\n\n'
    s1 += center('LUFIA II  CRESTING WAVE')
    s1 += '\n'
    s1 += center('Open World Randomizer')
    s1 += '\n\n'
    s1 += center('version {0}'.format(TEXT_VERSION))
    s1 += '\n\n\n'
    s1 += center('A Terror Wave Production')

    s2 = ''
    s2 += 'SEED    {0}\n'.format(num_to_text(get_seed()))
    s2 += 'FLAGS   {0}\n'.format(get_flags())
    randomness = {o.random_degree for o in ALL_OBJECTS}
    if len(randomness) == 1:
        randomness = int(round((sorted(randomness)[0]**0.5) * 100))
        s2 += 'CHAOS   {0}\n'.format(num_to_text(randomness))
    else:
        s2 += 'CHAOS   custom\n'
    difficulty = int(round(get_difficulty() * 100))
    s2 += 'DIFF    {0}\n'.format(num_to_text(difficulty))
    codes = get_activated_codes()
    if codes:
        codes = '\n        '.join(sorted(codes))
        s2 += 'CODES   {0}'.format(codes)
    s2 = '  ' + s2.replace('\n', '\n  ')

    boss_texts = {MapEventObject.get_script_by_signature(sig).pretty: sig
                  for sig in boss_events}

    def extract_location_boss(findstr):
        candidates = [b for b in boss_texts if findstr in b]
        if len(candidates) != 1:
            return None, None
        key = candidates[0]
        sig = boss_texts[key]
        map_index, _, _ = sig.split('-')
        map_index = int(map_index, 0x10)
        location = MapEventObject.get(map_index).zone_name
        boss = boss_matcher.findall(key)
        assert len(boss) == 1
        boss = BossFormationObject.get(int(boss[0], 0x10))
        return location, boss

    reward_item_order = [0x1a8, 0x1a7, 0x1aa, 0x1ab, 0x1c0, 0x1c1]
    reward_item_order += list(range(0x1b0, 0x1c0))

    boss_matcher = re.compile('\. 53\((..)\)')
    s3 = center('ITEM LOCATIONS')
    s3 += '\n\n\n'
    for item in reward_item_order:
        findstr = '. 2{0}({1:0>2X}-01)'.format(item >> 8, item & 0xFF)
        candidates = [b for b in boss_texts if findstr in b]
        assert len(candidates) <= 1
        if candidates:
            location, boss = extract_location_boss(findstr)
            s3 += ItemObject.get(item).name + '\n'
            s3 += right_justify(location) + '\n'
            s3 += right_justify(boss.boss.name) + '\n'
            s3 += '\n'

    s3 += '\n\n'

    maidens = ['Lisa', 'Marie', 'Clare']
    for maiden in maidens:
        findstr = 'My name is {0}'.format(maiden)
        location, boss = extract_location_boss(findstr)
        s3 += maiden + '\n'
        s3 += right_justify(location) + '\n'
        s3 += right_justify(boss.boss.name) + '\n'
        s3 += '\n'

    s3 += '\n\n'

    for character_index in range(7):
        findstr = '. 2B({0:0>2X})'.format(character_index)
        location, boss = extract_location_boss(findstr)
        if location is None or boss is None:
            continue
        s3 += CharacterObject.get(character_index).name + '\n'
        s3 += right_justify(location) + '\n'
        s3 += right_justify(boss.boss.name) + '\n'
        s3 += '\n'

    s3 += '\n\n'

    for capsule_index in range(7):
        findstr = '. 81({0:0>2X})'.format(capsule_index)
        location, boss = extract_location_boss(findstr)
        s3 += CapsuleObject.get(capsule_index*5).name + '\n'
        s3 += right_justify(location) + '\n'
        s3 += right_justify(boss.boss.name) + '\n'
        s3 += '\n'

    s3 += '\n\n'

    CONFLICT_ITEMS = [0x1c2, 0x1c5,
                      0x19c, 0x19d, 0x19e, 0x19f, 0x1a0,
                      0x1a1, 0x1a2, 0x1a3, 0x1a4]

    for item in CONFLICT_ITEMS:
        if item == iris_shop_item:
            location = iris_shop.zone_name
        else:
            candidates = [c for c in blue_chests if c.item.index == item]
            if candidates:
                assert len(candidates) == 1
                map_index = candidates[0].map_index
            else:
                candidates = []
                for t in thieves:
                    pretty = MapEventObject.get_script_by_signature(t).pretty
                    if ItemObject.get(item).name in pretty:
                        candidates.append(t)
                assert len(candidates) == 1
                map_index = int(candidates[0].split('-')[0], 0x10)
            location = MapEventObject.get(map_index).zone_name
        s3 += ItemObject.get(item).name + '\n'
        s3 += right_justify(location) + '\n'
        s3 += '\n'

    location = MapEventObject.get(wild_jelly_map).zone_name
    s3 += 'Master Jelly' + '\n'
    s3 += right_justify(location) + '\n'
    s3 += '\n'

    s4 = center('STAFF')
    s4 += '\n\n\n\n'
    roles = ['Creative Director', 'Game Experience Planning',
             'Reverse Engineering', 'Tools Development',
             'Director of Making Tia the\nProtagonist of the Game',
             'Testing and Debugging', 'Standards and Compliance',
             'Documentation', 'Assistant']

    for role in roles:
        s4 += role + '\n'
        s4 += right_justify('Abyssonym') + '\n\n\n'

    s4 += '\n\n\n'
    roles = [
        ('Fixxxer Patch Author', 'Relnqshd'),
        ('Legacy Documentation', 'Relnqshd'),
        ('Background Listening', 'Two Tone Tony'),
        ('Special Thanks', 'Lufia II Speedrun Community'),
        ]

    for role, person in roles:
        s4 += role + '\n'
        s4 += right_justify(person) + '\n\n\n'

    s4 += '\n\n\n\n\n\n\n'
    s4 += center('AND YOU')
    s4 = s4.rstrip()

    s = '\n\n\n\n\n\n\n'.join([s1, s2, s3, s4])

    final_string = b'\x02\x1d\x04\x03\x00\x01\x03\x20\x01\x02\x0f\x00'
    data = b'\x02\x01'
    newline_count = 0
    s = s.rstrip('\n')
    for line in s.split('\n'):
        if not line.strip():
            newline_count += 1
        else:
            if newline_count > 0:
                data += b'\x02' + bytes([newline_count])
            if len(line) >= 28:
                assert line[-1] != ' '
                data += b'\x01'
                line = line.lstrip()
            else:
                data += b'\x05'
                line = line.rstrip()
            data += line.encode('ascii') + b'\x00'
            newline_count = 0

    data += final_string
    #MAX_LENGTH = 1749
    #assert len(data) <= MAX_LENGTH

    old_credits_address = addresses.credits
    new_credits_address = 0x3ee100
    f = get_open_file(get_outfile())
    for i in range(1, 7):
        credits_pointer = getattr(addresses, 'credits_pointer%s' % i)
        f.seek(credits_pointer)
        temp = int.from_bytes(f.read(3), byteorder='little')
        assert map_from_lorom(temp) == old_credits_address
        f.seek(credits_pointer)
        f.write(int.to_bytes(map_to_lorom(new_credits_address),
                             length=3, byteorder='little'))
    f.seek(new_credits_address)
    test = f.read(len(data))
    assert len(set(test)) == 1
    f.seek(new_credits_address)
    f.write(data)


def get_ranked_locations(location_ranks, randoms_only=False):
    ranked_locations = []
    for i in sorted(location_ranks):
        locations = sorted(location_ranks[i])
        random.shuffle(locations)
        for loc in locations:
            if loc.endswith('1') or loc.endswith('2'):
                loc = loc[:-1]
            loc_properties = OpenNPCGenerator.get_properties_by_name(loc)
            if loc_properties is None:
                continue
            map_index = int(loc_properties.map_index, 0x10)
            meo = MapEventObject.get(map_index)
            if meo.zone_name not in ranked_locations:
                ranked_locations.append(meo.zone_name)

    temp = []
    for meo in MapEventObject.every:
        if meo.zone_name not in ranked_locations:
            continue
        if meo.zone_name in temp:
            continue
        s = str(meo)
        if '(FORMATION' in s:
            temp.append(meo.zone_name)
        elif 'Invoke Battle' in s and not randoms_only:
            temp.append(meo.zone_name)
    ranked_locations = [loc for loc in ranked_locations if loc in temp]

    return ranked_locations


def replace_map_formations(location_ranks=None):
    FormationObject.class_reseed('replace_map_formations')
    JELLY_SPRITE = 0x94
    SPRITE_OVERRIDES = {FormationObject.get(0): {0x36}}

    big_sprites = set(lange(0xb6, 0xbe) + lange(0xbf, 0xc9)
                      + lange(0xd2, 0xd5) + lange(0xeb, 0xf0))
    small_sprites = {s for s in range(0x80, 0xf0) if s not in big_sprites}
    all_formation_sprites = defaultdict(set)

    if location_ranks is not None:
        ranked_locations = get_ranked_locations(location_ranks,
                                                randoms_only=True)
    else:
        ranked_locations = None

    small_counts, big_counts = {}, {}
    for zone_index in sorted(MapEventObject.zone_names):
        meo = MapEventObject.get(zone_index)
        assert meo.zone_index == meo.index == zone_index
        zone_name = meo.zone_name
        zone_sprite_formations = meo.get_zone_enemies()
        sprites = {s for (s, f) in zone_sprite_formations if s != JELLY_SPRITE}
        my_small = {s for s in sprites if s in small_sprites}
        my_big = {s for s in sprites if s in big_sprites}
        small_counts[zone_name] = len(my_small)
        big_counts[zone_name] = len(my_big)
        for sprite, formation in zone_sprite_formations:
            all_formation_sprites[formation].add(sprite)

    for f in FormationObject.every:
        sprite = f.guess_sprite()
        if sprite is not None:
            all_formation_sprites[f].add(sprite)

    for f in SPRITE_OVERRIDES:
        all_formation_sprites[f] = SPRITE_OVERRIDES[f]

    cores = {0xa7, 0xa8, 0xa9, 0xaa}
    ranked_formations = [f for f in FormationObject.ranked if f.rank >= 0
                         and f in all_formation_sprites
                         and JELLY_SPRITE not in all_formation_sprites[f]
                         and not set(f.monster_indexes) & cores]
    small_formations = [f for f in ranked_formations
                        if all_formation_sprites[f] & small_sprites]
    big_formations = [f for f in ranked_formations
                      if all_formation_sprites[f] & big_sprites]
    shuffled = shuffle_simple(ranked_formations,
                              random_degree=FormationObject.random_degree)

    for zone_index in sorted(MapEventObject.zone_names):
        meo = MapEventObject.get(zone_index)
        assert meo.zone_index == meo.index == zone_index
        zone_name = meo.zone_name
        if ranked_locations is not None:
            if zone_name not in ranked_locations:
                continue
            rank = True
        else:
            rank = None

        zone_sprite_formations = meo.get_zone_enemies()
        sprites = {s for (s, f) in zone_sprite_formations if s != JELLY_SPRITE}
        formations = {f for (s, f) in zone_sprite_formations}
        my_small = {s for s in sprites if s in small_sprites}
        my_big = {s for s in sprites if s in big_sprites}
        new_sprite_map = {}
        new_formation_map = {}
        for spriteset in (my_small, my_big):
            if not spriteset:
                continue

            if rank is not None:
                if spriteset is my_big:
                    sub_ranked = [l for l in ranked_locations
                                  if big_counts[l] > 0]
                else:
                    sub_ranked = [l for l in ranked_locations
                                  if small_counts[l] > 0]
                assert zone_name in sub_ranked
                max_index = len(sub_ranked)-1
                rank = sub_ranked.index(zone_name) / max_index
                assert 0 <= rank <= 1

            if spriteset is my_small:
                valid_formations = small_formations
            else:
                valid_formations = big_formations

            for s in sorted(spriteset):
                candidate_formations = [
                    f for f in valid_formations if not
                    all_formation_sprites[f] & set(new_sprite_map.values())]

                if rank is None:
                    old_formations = [f for f in sorted(formations)
                                      if s in all_formation_sprites[f]]
                    if not old_formations:
                        continue
                    base = random.choice(old_formations)
                    new_formation = base.get_similar(
                        candidates=candidate_formations,
                        override_outsider=True)
                else:
                    reduced_shuffled = [f for f in shuffled
                                        if f in candidate_formations]
                    max_index = len(reduced_shuffled)-1
                    index = int(round(rank * max_index))
                    new_formation = reduced_shuffled[index]

                assert new_formation in valid_formations
                new_sprites = all_formation_sprites[new_formation]
                if len(new_sprites) > 1:
                    new_sprite = random.choice(sorted(new_sprites))
                else:
                    new_sprite = list(new_sprites)[0]

                assert s not in new_sprite_map
                new_sprite_map[s] = new_sprite
                assert new_sprite not in new_formation_map
                similar_formations = [
                    f for f in candidate_formations
                    if new_sprite in all_formation_sprites[f] and
                    set(f.clean_monsters) & set(new_formation.clean_monsters)]
                assert new_formation in similar_formations
                new_formation_map[new_sprite] = similar_formations

        for neighbor in meo.neighbors:
            mfo = MapFormationsObject.get(neighbor.index)
            signature = '{0:0>2X}-X-XX'.format(neighbor.index)
            script = neighbor.get_script_by_signature(signature)
            new_script = []
            for (l, o, p) in script.script:
                if o in {0x68, 0x7B}:
                    npc_event_index, sprite = p
                    if sprite in new_sprite_map:
                        if o == 0x68:
                            npcsig = '{0:0>2X}-C-{1:0>2X}'.format(
                                neighbor.index, npc_event_index)
                            nscript = neighbor.get_script_by_signature(npcsig)
                            if nscript is not None and '53(' in nscript.pretty:
                                new_script.append((l, o, p))
                                continue
                        new_sprite = new_sprite_map[sprite]
                        if o == 0x7B:
                            new_formation = random.choice(
                                new_formation_map[new_sprite])
                            formation_index = npc_event_index-0x50
                            assert formation_index >= 0
                            new_index = new_formation.index
                            mfo.formation_indexes[formation_index] = new_index
                        p = [npc_event_index, new_sprite]
                new_script.append((l, o, p))
            script.script = new_script


def scale_enemies(location_ranks, boss_events,
                  normal_scale_weight=0.75, boss_scale_weight=0.75):
    if scalecustom_nonboss is not None:
        normal_scale_weight = scalecustom_nonboss
    if scalecustom_boss is not None:
        boss_scale_weight = scalecustom_boss
    MapEventObject.class_reseed('scale_enemies')
    ranked_locations = get_ranked_locations(location_ranks)

    random.shuffle(boss_events)
    ranked_bosses = []
    for i, signature in enumerate(boss_events):
        map_index, _, _ = signature.split('-')
        map_index = int(map_index, 0x10)
        zone_name = MapEventObject.get(map_index).zone_name
        ranked_bosses.append((ranked_locations.index(zone_name), i, signature))
    ranked_bosses = [b for (l, i, b) in sorted(ranked_bosses)]

    formation_matcher = re.compile('#.*\(FORMATION (..): ')
    monster_ranks = defaultdict(list)
    for meo in MapEventObject.every:
        if meo.zone_name not in ranked_locations:
            continue
        rank = ranked_locations.index(meo.zone_name)
        formation_indexes = formation_matcher.findall(str(meo))
        for formation_index in formation_indexes:
            formation_index = int(formation_index, 0x10)
            formation = FormationObject.get(formation_index)
            for m in formation.monsters:
                if m is not None:
                    monster_ranks[m.index].append(rank)

    boss_matcher = re.compile('\. 53\((..)\)')
    boss_ranks = defaultdict(list)
    boss_accessories = set()
    bosses = {}
    for b in boss_events:
        map_index, _, _ = b.split('-')
        map_index = int(map_index, 0x10)
        zone_name = MapEventObject.get(map_index).zone_name
        rank = ranked_bosses.index(b)
        script = MapEventObject.get_script_by_signature(b)
        my_bosses = boss_matcher.findall(script.pretty)
        assert len(my_bosses) == 1
        boss = BossFormationObject.get(int(my_bosses[0], 0x10))
        for m in boss.monsters:
            boss_ranks[m.index].append(rank)
            if m is not boss.boss:
                boss_accessories.add(m)
            else:
                if m not in bosses:
                    bosses[m] = -1
                bosses[m] = max(bosses[m], boss.monsters.count(m))

    scale_dict = defaultdict(set)
    pre_ranked = MonsterObject.ranked
    for rankdict in (boss_ranks, monster_ranks):
        is_boss = rankdict == boss_ranks
        if rankdict is boss_ranks:
            scale_weight = boss_scale_weight
        else:
            scale_weight = normal_scale_weight
        temp = {}
        for m in rankdict:
            ranks = rankdict[m]
            lowest = min(ranks)
            avg = sum(ranks) / len(ranks)
            if is_boss:
                temp[m] = lowest
            else:
                temp[m] = avg
        rankdict = temp

        monsters = [m for m in MonsterObject.every if m.index in rankdict]
        monsters_expected = sorted(
            monsters, key=lambda m: (rankdict[m.index], m.signature))
        monsters_actual = [m for m in pre_ranked if m in monsters]

        max_index = len(monsters)-1
        for m in monsters:
            if m in bosses and not is_boss:
                continue
            expected = monsters_expected.index(m)
            actual = monsters_actual.index(m)

            if m in bosses and bosses[m] > 1:
                augmented_rank = m.rank * (bosses[m] ** 0.5)
                below = [m for m in monsters_actual
                         if m.rank < augmented_rank]
                if below:
                    new_actual = len(below) - 0.5
                    assert actual < new_actual
                    modifier = actual / new_actual
                    assert modifier < 1
                    expected = int(round(modifier * expected))

            target = monsters_actual[expected]
            ratios = []
            for attr in sorted(target.mutate_attributes):
                if attr in ('gold', 'xp'):
                    continue
                a = m.old_data[attr]
                b = target.old_data[attr]
                if a == 0:
                    continue
                ratio = b / a
                if expected > actual:
                    ratio = max(ratio, 1.0)
                if expected < actual:
                    ratio = min(ratio, 1.0)
                ratios.append(ratio)
            factor = sum(ratios) / len(ratios)

            scale_amount = factor ** scale_weight
            scale_dict[m.index].add(scale_amount)

    for m in MonsterObject.every:
        if m.index not in scale_dict:
            continue

        scale_amounts = scale_dict[m.index]
        if m in boss_accessories:
            scale_amount = min(scale_amounts)
        else:
            assert len(scale_amounts) == 1
            scale_amount = list(scale_amounts)[0]

        m.scale_stats(scale_amount)


def make_spoiler(ir):
    head, tail = path.split(get_outfile())
    outfilename = path.join(head, 'spoiler.{0}.txt'.format(tail))
    randomness = [o.random_degree for o in ALL_OBJECTS]
    if len(set(randomness)) == 1:
        randomness = list(set(randomness))
    s = ('LUFIA 2 CRESTING WAVE OPEN WORLD RANDOMIZER',
         'version: {}'.format(VERSION),
         'seed: {}'.format(get_seed()),
         'flags: {}'.format(get_flags()),
         'codes: {}'.format(','.join(sorted(get_activated_codes()))),
         'randomness: {}'.format(','.join(str(r) for r in randomness)),
         'difficulty: {}'.format(get_difficulty()),
         )
    header = '\n'.join(s)
    footer = ir.report
    with open(outfilename, 'w+') as f:
        f.write('{0}\n\n{1}\n'.format(header, footer))


def make_open_world(custom=None):
    # new coin shop on forfeit island (only supports coins + 3 items)
    s = ShopObject.get(0x1a)
    s.become_coin_shop()
    s.wares['coin'] = [0x18d]
    s.wares['item'] = [0xb, 0xc, 0xd]

    patch_events('max_world_clock', warn_double_import=False)
    patch_events('open_world_base', warn_double_import=False)
    for line in read_lines_nocomment(path.join(tblpath, 'priests.txt')):
        OpenNPCGenerator.create_priest(line)

    for clo in CharLevelObject.every:
        clo.level = 5

    for clo in CapsuleLevelObject.every:
        clo.level = 5

    for cxp in CharExpObject.every:
        cxp.xp = 212

    for ieo in InitialEquipObject.every:
        ieo.set_appropriate_initial_equipment()

    for rno in RoamingNPCObject.every:
        rno.map_index = 0xff

    for meo in MapEventObject.every:
        if meo.zone_name in {
                'Overworld', 'Seafloor', 'Karlloon Shrine', 'Daos Shrine'}:
            meo.change_escapability(make_escapable=False)
        else:
            meo.change_escapability(make_escapable=True)

    NOBOSS_LOCATIONS = {'starting_character', 'starting_item'}
    MapEventObject.class_reseed('item_route')
    ir = ItemRouter(path.join(tblpath, 'requirements.txt'),
                    path.join(tblpath, 'restrictions.txt'))
    if custom is not None:
        custom_assignments = {}
        for line in read_lines_nocomment(custom):
            while '  ' in line:
                line = line.replace('  ', ' ')
            line = line.strip()
            if not line:
                continue
            location, item = line.split(' ')
            custom_assignments[location] = item
        ir.set_custom_assignments(custom_assignments)
    ir.assign_everything()
    if 'starting_item' not in ir.assignments:
        ir.assignments['starting_item'] = 'dragon_egg'
    assert 'daos_shrine' not in ir.assignments
    ir.assignments['daos_shrine'] = 'victory'
    make_spoiler(ir)

    assigned_item_indexes = []

    name = ir.assignments['starting_item']
    starting_item = OpenNPCGenerator.get_properties_by_name(name)
    index = int(starting_item.item_index, 0x10)
    assigned_item_indexes.append(index)
    starting_item = OpenNPCGenerator.set_appropriate_item_icon(starting_item)

    name = ir.assignments['starting_character']
    starting_character = OpenNPCGenerator.get_properties_by_name(name)
    dual_blade = ItemObject.get(0x36)
    dual_blade.equipability = 0
    dual_blade.set_bit(starting_character.name, True)

    warp = SpellObject.get(0x24)
    warp.characters |= 0x7f
    warp.mp_cost = 0

    starting_item_reward_event = OpenNPCGenerator.REWARD_EVENT_ITEM
    item_index = int(starting_item.item_index, 0x10)
    item_acquire_opcode = '21' if item_index >= 0x100 else '20'
    item_acquire_opcode = '{0}({1:0>2X}-01)'.format(
            item_acquire_opcode, item_index & 0xFF)
    final_boss_flag = OpenNPCGenerator.available_flags.pop()
    iris_ending_flag = OpenNPCGenerator.available_flags.pop()
    jelly_flag = OpenNPCGenerator.available_flags.pop()
    ending_npcs = [0x50, 0x51, 0x52]
    random.shuffle(ending_npcs)
    a, b, c = ending_npcs
    male_titles = {'Czar', 'Duke', 'Emperor', 'King', 'Lord', 'Master'}
    female_titles = {'Czarina', 'Duchess', 'Empress',
                     'Queen', 'Lady', 'Mistress'}
    unisex_titles = {'Sovereign'}
    if starting_character.name in {'selan', 'tia'}:
        candidates = female_titles | unisex_titles
    else:
        assert starting_character.name in {'maxim', 'guy', 'dekar'}
        candidates = male_titles | unisex_titles
    ending_title = random.choice(sorted(candidates))
    starting_character_index = int(starting_character.character_index, 0x10)
    parameters = {
        'reward_id': '',
        'item_icon_code': starting_item.item_icon_code,
        'item_display_name': starting_item.item_display_name,
        'item_acquire_opcode': item_acquire_opcode,
        'starting_character_index': starting_character_index,
        'starting_character_flag': starting_character_index+1,
        'starting_item_reward_event': starting_item_reward_event,
        'final_boss_flag': final_boss_flag,
        'iris_ending_flag': iris_ending_flag,
        'ending_npc_a': a,
        'ending_npc_b': b,
        'ending_npc_c': c,
        'ending_title': ending_title,
        'jelly_flag': jelly_flag,
        }
    OverSpriteObject.become_character(
        int(starting_character.character_index, 0x10))

    OpenNPCGenerator.create_karlloon_elf_girl(parameters)
    OpenNPCGenerator.create_egg_girl(parameters)

    MapEventObject.class_reseed('boss_route1')
    sorted_locations = []
    for rank in sorted(ir.location_ranks):
        locs = set(ir.location_ranks[rank])
        locs = sorted(locs)
        random.shuffle(locs)
        for l in locs:
            if l not in ir.assignments:
                continue
            key = l.rstrip('1').rstrip('2')
            if l in NOBOSS_LOCATIONS or key in NOBOSS_LOCATIONS:
                continue
            if key in sorted_locations:
                continue
            sorted_locations.append(key)

    bosses = sorted(OpenNPCGenerator.boss_properties.values(),
                    key=lambda b: b.name)
    random.shuffle(bosses)
    chosen_bosses = []
    spare_formations = []
    done_bosses = set()
    for b in bosses:
        key = b.name
        if key[-1] in '0123456789':
            key = key[:-1]
        b = BossFormationObject.get(int(b.boss_formation_index, 0x10))
        if key in done_bosses:
            spare_formations.append(b)
            continue
        chosen_bosses.append(b)
        done_bosses.add(key)

    old_formations = {bfo.name for bfo in BossFormationObject.uniques}
    new_formations = set()
    seed_monsters = [MonsterObject.get(i)
                     for i in BossFormationObject.DUMMIED_MONSTERS]
    SCRAP_FORMATIONS = [3, 4, 0x10, 0x11]
    for bfo in BossFormationObject.every:
        if bfo.index in SCRAP_FORMATIONS and bfo not in spare_formations:
            spare_formations.append(bfo)

    for ipa in IPAttackObject.every:
        ipa.replace_banned_animation()

    for f in spare_formations:
        for i in range(1000):
            f.reseed('become%s' % i)
            if seed_monsters:
                f.become_random(seed_monsters.pop())
            else:
                f.become_random()
            if f.name not in old_formations | new_formations:
                new_formations.add(f.name)
                break

    del(BossFormationObject._class_property_cache['ranked'])
    MapEventObject.class_reseed('boss_route2')
    chosen_bosses = chosen_bosses + spare_formations
    random.shuffle(chosen_bosses)
    chosen_bosses = chosen_bosses[:len(sorted_locations)]
    while len(chosen_bosses) < len(sorted_locations):
        chosen_bosses.append(random.choice(chosen_bosses))
    sorted_bosses = sorted(chosen_bosses, key=lambda b: (b.rank, b.index))
    sorted_bosses = shuffle_simple(
        sorted_bosses, random_degree=BossFormationObject.random_degree)

    assert len(sorted_bosses) == len(sorted_locations)
    location_bosses = {l: b for (l, b) in zip(sorted_locations, sorted_bosses)}
    final_boss = location_bosses['daos_shrine']
    parameters['final_boss_sprite_index'] = final_boss.guess_sprite()

    # Apply base patches BEFORE procedural modifications
    patch_with_template('open_world_events', parameters)

    boss_events = []
    assert len(sorted_bosses) == len(sorted_locations)
    for location, boss in sorted(location_bosses.items()):
        reward1, reward2 = None, None
        if location in ir.assignments:
            reward1 = ir.assignments[location]
        key = '%s1' % location
        if key in ir.assignments:
            assert reward1 is None
            reward1 = ir.assignments[key]
        key = '%s2' % location
        if key in ir.assignments:
            reward2 = ir.assignments[key]
        assert reward1 or reward2
        result = OpenNPCGenerator.create_boss_npc(location, boss,
                                                  reward1, reward2, parameters)
        location, boss, reward1, reward2, event = result
        boss_events.append(event)
        for reward in reward1, reward2:
            if hasattr(reward, 'item_index'):
                assigned_item_indexes.append(int(reward.item_index,
                                                 0x10))

    for location in sorted(OpenNPCGenerator.boss_location_properties):
        if location not in OpenNPCGenerator.done_locations:
            OpenNPCGenerator.create_prince(location)

    if 'monstermash' in get_activated_codes():
        replace_map_formations(ir.location_ranks)

    if (('scale' in get_activated_codes() or 'm' in get_flags()) and
            'noscale' not in get_activated_codes()):
        scale_enemies(ir.location_ranks, boss_events)

    FILLER_ITEM = 0x2b
    EXTRA_CHESTS = [0x21, 0x2f]
    for i in EXTRA_CHESTS:
        ChestObject.get(i).set_item(0x2b)

    MapEventObject.class_reseed('iris_items')
    conflict_chests = [c for c in ChestObject.every
                       if c.item_index in assigned_item_indexes
                       and c.item_index != FILLER_ITEM]
    conflict_chests.append(ChestObject.get(0x21))
    CONFLICT_ITEMS = [0x19c, 0x19d, 0x19e, 0x19f, 0x1a0,
                      0x1a1, 0x1a2, 0x1a3, 0x1a4,
                      0x1c2, 0x1c5]
    IRIS_ITEMS = sorted(range(0x19c, 0x1a4))
    iris_shop_item, iris_thief_item = random.sample(IRIS_ITEMS, 2)
    CONFLICT_ITEMS.remove(iris_shop_item)
    CONFLICT_ITEMS.remove(iris_thief_item)

    iris_shop = assign_iris_shop(iris_shop_item)
    conflict_items = sorted(CONFLICT_ITEMS)
    while len(conflict_items) < len(conflict_chests):
        conflict_items.append(FILLER_ITEM)
    random.shuffle(conflict_items)
    for chest, item in zip(conflict_chests, conflict_items):
        chest.set_item(item)

    thieves = generate_thieves(iris_thief_item)

    iris_iris = (iris_shop_item, iris_shop)
    wild_jelly_map = make_wild_jelly(jelly_flag)
    generate_hint_npcs(boss_events, conflict_chests, wild_jelly_map,
                       iris_iris, thieves)
    OpenNPCGenerator.create_hint_shop(conflict_chests, wild_jelly_map,
                                      iris_iris, thieves)
    apply_iris_wards(MapEventObject.get(0x8c).neighbors,
                     wild_jelly_map=wild_jelly_map)
    write_credits(boss_events, conflict_chests, wild_jelly_map,
                  (iris_shop_item, iris_shop), thieves)

    write_patch(get_outfile(), 'patch_no_boat_encounters.txt')
    write_patch(get_outfile(), 'patch_maximless_warp_animation_fix.txt')
    write_patch(get_outfile(), 'patch_maximless_boat_fix.txt')
    write_patch(get_outfile(), 'patch_zero_capsule_command.txt')
    write_patch(get_outfile(), 'patch_start_portravia.txt')
    write_patch(get_outfile(), 'patch_no_submarine.txt')
    write_patch(get_outfile(), 'patch_spell_target_limit.txt')
    write_patch(get_outfile(), 'patch_capsule_feeding_bonus.txt')
    if 'nocap' not in get_activated_codes():
        write_patch(get_outfile(), 'patch_capsule_tag.txt')

    dragon_egg = ItemObject.get(0x2b)
    dragon_egg.price = 65000
    write_patch(get_outfile(), 'patch_eat_dragon_eggs.txt')

    set_new_leader_for_events(int(starting_character.character_index, 0x10))

    MapEventObject.purge_orphans()


def dump_events(filename):
    s = ''
    for meo in MapEventObject.every:
        s += str(meo) + '\n\n'

    with open(filename, 'w+') as f:
        f.write(s)

    return s


class VanillaObject(TableObject):
    flag = 'v'
    flag_description = 'nothing'


ALL_OBJECTS = [g for g in globals().values()
               if isinstance(g, type) and issubclass(g, TableObject)
               and g not in [TableObject]]


def key_shop():
    tower = {'sky', 'wind', 'cloud', 'light', 'trial', 'truth', 'narcysus'}
    shrine = {'sword', 'heart', 'ghost'}
    dungeon = {'lake', 'ruby', 'dankirk', 'basement', 'ancient'}
    mountain = {'magma', 'flower', 'tree'}

    keys = lange(0x1af, 0x1c0) + [0x1c2]
    keys = [ItemObject.get(key) for key in keys]
    keys = sorted(keys, key=lambda k: k.name)

    tower_keys = [k for k in keys if k.name.lower().split()[0] in tower]
    shrine_keys = [k for k in keys if k.name.lower().split()[0] in shrine]
    dungeon_keys = [k for k in keys if k.name.lower().split()[0] in dungeon]
    mountain_keys = [k for k in keys if k.name.lower().split()[0] in mountain]
    assert len(tower_keys) == len(tower)
    assert len(shrine_keys) == len(shrine)
    assert len(dungeon_keys) == len(dungeon)
    assert len(mountain_keys) == len(mountain)

    keydict = {
        'tower': tower_keys,
        'shrine': shrine_keys,
        'dungeon': dungeon_keys,
        'mountain': mountain_keys,
        }

    s = ''
    for i, location in enumerate(['dungeon', 'mountain', 'shrine', 'tower']):
        line_number = (i+1)*0x1000
        keys = keydict[location]
        key_lines = {key: line_number + ((k+1) * 0x100) for (k, key) in enumerate(keys)}
        page_keys = sorted(keys, key=lambda k: k.name)
        while len(page_keys) > 0:
            if len(page_keys) <= 4:
                my_page = page_keys
                page_keys = []
            else:
                my_page = page_keys[:3]
                page_keys = page_keys[3:]
            addresses = [key_lines[key] for key in my_page]
            if page_keys:
                next_page_line = line_number + 0x30
                addresses.append(next_page_line)
                s += '{0:0>4X}. 10({1:0>2X}'.format(line_number, len(addresses))
                for addr in addresses:
                    s += '-@{0:X}'.format(addr)
                s += ')\n'
                line_number += 0x10
                s += '{0:0>4X}. 08: '.format(line_number)
                for key in my_page:
                    s += '{0}\n'.format(key.name)
                s += 'Next page<CHOICE>\n'
                line_number += 0x10
            else:
                s += '{0:0>4X}. 10({1:0>2X}'.format(line_number, len(addresses))
                for addr in addresses:
                    s += '-@{0:X}'.format(addr)
                s += ')\n'
                line_number += 0x10
                s += '{0:0>4X}. 08: '.format(line_number)
                for key in my_page:
                    s += '{0}\n'.format(key.name)
                s = s.rstrip('\n') + '<CHOICE>\n'
                line_number += 0x10
            s += '{0:0>4X}. 1C(@MENU_CANCEL)\n'.format(line_number)
            line_number += 0x10
        for key in keys:
            line_number = key_lines[key]
            key_index = key.index
            s += '{0:0>4X}. 14(C2-{1:0>4X}-0001-20-@ALREADY_HAVE-FF)\n'.format(
                line_number, key_index)
            line_number += 0x10
            s += '{0:0>4X}. 21({1:0>2X}-01)\n'.format(line_number, key_index & 0xFF)
            line_number += 0x10
            s += '{0:0>4X}. 24(2B-03)\n'.format(line_number)
            line_number += 0x10
            s += ("{0:0>4X}. 08: You got it. Here's\n"
                                "your {1}.<END MESSAGE>\n").format(line_number, key.name)
            line_number += 0x10
            s += '{0:0>4X}. '.format(line_number)
            s += '4B(33)\n'
            line_number += 0x10
            s += '{0:0>4X}. '.format(line_number)
            s += '8C(01-0A-08)\n'
            line_number += 0x10
            s += '{0:0>4X}. '.format(line_number)
            s += '86(00-40)\n'
            line_number += 0x10
            s += '{0:0>4X}. '.format(line_number)
            s += '49(C8)\n'
            line_number += 0x10
            s += '{0:0>4X}. '.format(line_number)
            s += '9E: <POSITION 02>Gets the\n{0}.<END MESSAGE>\n'.format(key.name)
            line_number += 0x10
            s += '{0:0>4X}. 1C(@FINISH_BUY_KEY)\n'.format(line_number)
    return s


if __name__ == '__main__':
    try:
        print ('You are using the Lufia II '
               'randomizer version %s.\n' % VERSION)

        codes = {
            'anywhere': ['anywhere'],
            #'everywhere': ['everywhere'],
            'personnel': ['nothingpersonnelkid', 'nothing.personnel.kid',
                          'nothing personnel kid', 'nothing_personnel_kid'],
            'easymodo': ['easymodo'],
            'holiday': ['holiday'],
            'open': ['open', 'openworld'],
            'custom': ['custom'],
            'airship': ['airship'],
            'splitscale': ['splitscale'],
            'scale': ['scale'],
            'noscale': ['noscale'],
            'bossy': ['bossy'],
            'monstermash': ['monstermash'],
            'nocap': ['nocap'],
        }
        run_interface(ALL_OBJECTS, snes=True, codes=codes,
                      custom_degree=True, custom_difficulty=True)
        numify = lambda x: '{0: >3}'.format(x)
        minmax = lambda x: (min(x), max(x))

        if 'personnel' in get_activated_codes():
            print('NOTHING PERSONNEL KID.')

        patch_events()
        MapEventObject.roaming_comments = set()

        if 'bossy' in get_activated_codes():
            BossFormationObject.random_degree = 1.0
            if 'noscale' not in get_activated_codes():
                scalecustom_boss = 1.0
                activate_code('scale')

        if 'splitscale' in get_activated_codes():
            print('NOTE: 0.75 for the standard scaling value, '
                  '0.0 for no scaling.')
            scalecustom_boss = input(
                'Please enter the scaling multiplier for bosses: ')
            scalecustom_nonboss = input(
                'Please enter the scaling multiplier for nonbosses: ')
            scalecustom_boss = float(scalecustom_boss.strip())
            scalecustom_nonboss = float(scalecustom_nonboss.strip())
            activate_code('scale')

        if check_open_world():
            if 'airship' in get_activated_codes():
                custom = path.join(tblpath, 'custom_airship.txt')
            elif 'custom' in get_activated_codes():
                custom = input(
                    'Please enter the filepath of your custom seed: ')
            else:
                custom = None
            make_open_world(custom=custom)
        else:
            if 'monstermash' in get_activated_codes():
                replace_map_formations()

        clean_and_write(ALL_OBJECTS)
        dump_events('_l2r_event_dump.txt')

        rewrite_snes_meta('L2-R', int(VERSION[0]), lorom=True)
        finish_interface()
    except Exception:
        print(format_exc())
        input('Press Enter to close this program.')
