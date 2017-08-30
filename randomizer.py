from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses,
    mutate_normal, shuffle_normal, get_random_degree)
from randomtools.utils import (
    classproperty, get_snes_palette_transformer,
    read_multi, write_multi, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, run_interface, rewrite_snes_meta,
    clean_and_write, finish_interface)
from collections import defaultdict
from os import path
from time import time
from collections import Counter


VERSION = 1
ALL_OBJECTS = None
DEBUG_MODE = False


class AdditionalPropertiesMixin(object):
    def read_data(self, filename=None, pointer=None):
        super(AdditionalPropertiesMixin, self).read_data(filename, pointer)

        offset = self.pointer + self.total_size
        self.additional_addresses = {}
        self.additional_properties = {}
        bitnames = [bn for bns in self.additional_bitnames
                    for bn in self.bitnames[bns]]

        f = open(filename, "r+b")
        for bitname in bitnames:
            if self.get_bit(bitname):
                self.additional_addresses[bitname] = offset
                f.seek(offset)
                value = read_multi(f, length=2)
                self.additional_properties[bitname] = value
                offset += 2
        f.close()

        if self.index > 0:
            prev = ItemObject.get(self.index-1)
            if prev.additional_addresses:
                assert self.pointer > max(prev.additional_addresses.values())

    def write_data(self, filename=None, pointer=None):
        super(AdditionalPropertiesMixin, self).write_data(filename, pointer)

        bitnames = [bn for bns in self.additional_bitnames
                    for bn in self.bitnames[bns]]

        f = open(filename, "r+b")
        for bitname in bitnames:
            if self.get_bit(bitname):
                offset = self.additional_addresses[bitname]
                value = self.additional_properties[bitname]
                f.seek(offset)
                write_multi(f, value, length=2)
                offset += 2
            else:
                assert bitname not in self.additional_addresses
                assert bitname not in self.additional_properties
        f.close()


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
        if price > 10 and price % 10 == 0:
            price = price - 1
        self.price = price


class CapsuleObject(TableObject):
    flag = 'p'
    flag_description = "capsule monsters"

    intershuffle_attributes = [
        ("hp", "hp_factor"),
        "attack",
        "defense",
        ("strength", "strength_factor"),
        ("agility", "agility_factor"),
        ("intelligence", "intelligence_factor"),
        ("guts", "guts_factor"),
        ("magic_resistance", "magic_resistance_factor"),
        ]
    mutate_attributes = {
        "hp": None,
        "hp_factor": None,
        "attack": None,
        "defense": None,
        "strength": None,
        "strength_factor": None,
        "agility": None,
        "agility_factor": None,
        "intelligence": None,
        "intelligence_factor": None,
        "guts": None,
        "guts_factor": None,
        "magic_resistance": None,
        "magic_resistance_factor": None,
    }

    @property
    def name(self):
        return self.name_text.strip()

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
        start = CapsuleObject.specspointer
        for i, (pointer, sprite, palette) in enumerate(
                zip(pointers, sprites, palettes)):
            c = CapsuleObject.get(i)
            f = open(get_outfile(), "r+b")
            f.seek(start + (2*c.index))
            write_multi(f, pointer-start, length=2)
            c.pointer = pointer
            f.close()
            c.read_data(filename=get_outfile(), pointer=c.pointer)
            CapSpritePTRObject.get(i).sprite_pointer = sprite
            CapPaletteObject.get(i).set_all_colors(palette)

    @classmethod
    def full_randomize(cls):
        CapsuleObject.class_reseed("full")
        ordering = []
        for c in CapsuleObject.every:
            candidates = [c2.index for c2 in CapsuleObject.every
                          if c2.capsule_class == c.capsule_class]
            candidates = [c2 for c2 in candidates if c2 not in ordering]
            ordering.append(random.choice(candidates))
        CapsuleObject.reorder_capsules(ordering)
        super(CapsuleObject, cls).full_randomize()


class CapSpritePTRObject(TableObject): pass


class CapPaletteObject(TableObject):
    def get_all_colors(self):
        colors = []
        for i in xrange(0x10):
            c = getattr(self, "color%X" % i)
            colors.append(c)
        return colors

    def set_all_colors(self, colors):
        for i, c in enumerate(colors):
            setattr(self, "color%X" % i, c)


class ChestObject(TableObject):
    flag = 't'
    flag_description = "treasure chests"

    @property
    def item_index(self):
        return (
            self.get_bit("item_high_bit") << 8) | self.item_low_byte

    @property
    def item(self):
        return ItemObject.get(self.item_index)

    def set_item(self, item):
        if isinstance(item, ItemObject):
            item = item.index
        if item & 0x100:
            self.set_bit("item_high_bit", True)
        else:
            self.set_bit("item_high_bit", False)
        self.item_low_byte = item & 0xFF

    def mutate(self):
        i = self.item.get_similar()
        self.set_item(i)


class SpellObject(PriceMixin, TableObject):
    flag = 'l'
    flag_description = "learnable spells"

    mutate_attributes = {
        "price": None,
        "mp_cost": None,
    }

    @property
    def name(self):
        return self.name_text.strip()

    @classproperty
    def after_order(self):
        if 'c' in get_flags():
            return [CharacterObject]
        return []

    @staticmethod
    def intershuffle():
        SpellObject.class_reseed("inter")
        old_casters = []
        for i in xrange(7):
            mask = (1 << i)
            charmasks = [s.characters & mask for s in SpellObject.every]
            if not any(charmasks):
                continue
            old_casters.append(i)
            num_learnable = len([c for c in charmasks if c])
            num_learnable = mutate_normal(num_learnable, 1, len(charmasks),
                                          wide=True)
            charmasks = [mask if i < num_learnable else 0
                         for i in xrange(len(charmasks))]
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

        new_casters = [i for i in xrange(7)
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
        return self.old_data["price"]

    def cleanup(self):
        self.price_clean()


class CharGrowthObject(TableObject):
    flag = 'c'

    mutate_attributes = {
        "hp": None,
        "mp": None,
        "str": None,
        "agl": None,
        "int": None,
        "gut": None,
        "mgr": None,
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

    def mutate(self):
        super(CharGrowthObject, self).mutate()


class CharacterObject(TableObject):
    flag = 'c'
    flag_description = "characters"

    @property
    def name(self):
        return {0: "Maxim",
                1: "Selan",
                2: "Guy",
                3: "Artea",
                4: "Tia",
                5: "Dekar",
                6: "Lexis"}[self.index]

    @staticmethod
    def intershuffle():
        CharacterObject.class_reseed("inter")
        indexes = [c.index for c in CharacterObject.every]
        ordering = list(indexes)
        random.shuffle(ordering)

        for (ai, bi) in zip(indexes, ordering):
            aa = CharGrowthObject.get_character(ai)
            bb = CharGrowthObject.get_character(bi)
            for (a, b) in zip(aa, bb):
                for key in CharGrowthObject.mutate_attributes:
                    bv = b.old_data[key]
                    setattr(a, key, bv)

            a = CharacterObject.get(ai)
            b = CharacterObject.get(bi)
            for key in CharGrowthObject.mutate_attributes:
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
    flag_description = "monsters"

    intershuffle_attributes = [
        "hp", "attack", "defense", "agility", "intelligence",
        "guts", "magic_resistance", "xp", "gold"]

    mutate_attributes = {
        "level": None,
        "hp": None,
        "attack": None,
        "defense": None,
        "agility": None,
        "intelligence": None,
        "guts": None,
        "magic_resistance": None,
        "xp": None,
        "gold": None,
    }

    @property
    def intershuffle_valid(self):
        return self.rank >= 0 and not 0xA7 <= self.index <= 0xAA

    @property
    def name(self):
        return self.name_text.strip()

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
        if hasattr(self, "_rank"):
            return self._rank
        rankdict = {
            0xdf: -1,
            }
        if self.index in rankdict:
            self._rank = rankdict[self.index]
        else:
            assert self.level * self.hp * self.xp != 0
            self._rank = self.level * self.hp * self.xp
        return self.rank

    @classmethod
    def intershuffle(cls):
        MonsterObject.class_reseed("inter")
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
        if self.has_drop:
            f = open(filename, "r+b")
            f.seek(self.pointer+self.total_size)
            self.drop_data = read_multi(f, length=2)
            f.close()

    def write_data(self, filename=None, pointer=None):
        super(MonsterObject, self).write_data(filename, pointer)
        if self.has_drop:
            f = open(filename, "r+b")
            f.seek(self.pointer+self.total_size)
            write_multi(f, self.drop_data, length=2)
            f.close()

    def mutate(self):
        super(MonsterObject, self).mutate()
        if self.has_drop:
            i = self.drop.get_similar()
            self.set_drop(i)

    def cleanup(self):
        if self.is_boss:
            for attr in self.old_data:
                if getattr(self, attr) < self.old_data[attr]:
                    setattr(self, attr, self.old_data[attr])


class ItemObject(AdditionalPropertiesMixin, PriceMixin, TableObject):
    flag = 'i'
    flag_description = "items and equipment"

    additional_bitnames = ['misc1', 'misc2']
    mutate_attributes = {
        "price": None,
    }

    @property
    def name(self):
        return ItemNameObject.get(self.index).name_text.strip()

    @property
    def is_coin_set(self):
        return 0x18a <= self.index <= 0x18d

    @property
    def is_coin_item(self):
        for s in ShopObject.every:
            if s.wares["coin"] and self.index in s.wares["item"]:
                return True
        return False

    @property
    def alt_cursed(self):
        if self.get_bit("cursed"):
            return ItemObject.get(self.index+1)
        elif self.index == 0:
            return None
        else:
            test = ItemObject.get(self.index-1)
            if test.get_bit("cursed"):
                return test
        return None

    @property
    def rank(self):
        if hasattr(self, "_rank"):
            return self._rank

        price = self.old_data["price"]

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
        if self.index in rankdict:
            self._rank = rankdict[self.index]
        elif 0x18e <= self.index <= 0x19b:
            self._rank = price * 2000
        elif price <= 2 or self.get_bit("unsellable"):
            self._rank = -1
        elif self.alt_cursed:
            self._rank = max(price, self.alt_cursed.price)
        else:
            self._rank = price
        self._rank = min(self._rank, 65000)
        return self.rank

    def cleanup(self):
        if self.is_coin_item:
            self.price = min(self.price, 2500)
            return
        self.price_clean()

    @staticmethod
    def intershuffle():
        ItemObject.class_reseed("inter")
        candidates = [i for i in ItemObject.ranked
                      if "ip_effect" in i.additional_properties]
        negranks = [c for c in candidates if c.rank < 0]
        for c in negranks:
            candidates.remove(c)
            assert c not in candidates
            max_index = len(candidates)
            index = random.randint(random.randint(random.randint(
                0, max_index), max_index), max_index)
            candidates.insert(index, c)
        shuffled = shuffle_normal(candidates,
                                  random_degree=(get_random_degree() ** 0.25))
        shuffled = [i.additional_properties["ip_effect"] for i in shuffled]
        for i, ip in zip(candidates, shuffled):
            i.additional_properties["ip_effect"] = ip

        for equip_type in ["weapon", "armor", "shield",
                           "helmet", "ring", "jewel"]:
            equips = [i for i in ItemObject.every
                      if i.get_bit("equipable") and i.get_bit(equip_type)]
            ordering = range(7)
            random.shuffle(ordering)
            for i in equips:
                old_equip = i.equipability
                assert not (old_equip & 0x80)
                new_equip = 0
                for n, m in enumerate(ordering):
                    if bool(old_equip & (1 << m)):
                        new_equip |= (1 << n)
                if random.random() < (get_random_degree() ** 4):
                    new_equip = new_equip | (random.randint(0, 0x7f) &
                                             random.randint(0, 0x7f))
                if random.random() < (get_random_degree() ** 2):
                    temp = new_equip & (random.randint(0, 0x7f) |
                                        random.randint(0, 0x7f))
                    if temp:
                        new_equip = temp
                i.equipability = new_equip

    @classmethod
    def mutate_all(cls):
        super(ItemObject, cls).mutate_all()
        addprops = ["increase_atp", "increase_dfp", "increase_str",
                    "increase_agl", "increase_int", "increase_gut",
                    "increase_mgr"]
        minmaxes = {}
        for ap in addprops:
            candidates = [i for i in ItemObject.every
                          if ap in i.additional_properties]
            assert candidates
            values = [c.additional_properties[ap] for c in candidates]
            minmaxes[ap] = (min(values), max(values))

        for i in ItemObject.every:
            i.reseed(salt="mut2")
            for ap in addprops:
                if ap not in i.additional_properties:
                    continue
                lower, upper = minmaxes[ap]
                value = i.additional_properties[ap]
                value = mutate_normal(value, lower, upper)
                i.additional_properties[ap] = value


class ShopObject(TableObject):
    flag = 's'
    flag_description = "shops"

    def __repr__(self):
        s = "SHOP %x\n" % self.index
        for menu in ["coin", "item", "weapon", "armor"]:
            if self.get_bit(menu):
                s += "%s\n" % menu.upper()
                for value in self.wares[menu]:
                    i = ItemObject.get(value)
                    s += "{0:12} {1}\n".format(i.name, i.price)
        if self.get_bit("spell"):
            s += "SPELL\n"
            for value in self.spells:
                s += "%s\n" % SpellObject.get(value).name
        return s.strip()

    @property
    def wares_flat(self):
        flat = []
        for menu in ["item", "weapon", "armor"]:
            flat.extend(self.wares[menu])
        return [ItemObject.get(v) for v in flat]

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
        if hasattr(ShopObject, "_shoppable_items"):
            return ShopObject._shoppable_items

        assert hasattr(ItemObject.get(1), "_rank")
        shoppable_items = list(ShopObject.shop_items)
        for i in ItemObject.every:
            if (i not in shoppable_items and not i.get_bit("unsellable")
                    and i.rank == i.old_data["price"] and i.price > 0
                    and not i.is_coin_set):
                shoppable_items.append(i)
        shoppable_items = sorted(shoppable_items, key=lambda i: i.index)
        ShopObject._shoppable_items = shoppable_items
        return ShopObject.shoppable_items

    def read_data(self, filename=None, pointer=None):
        super(ShopObject, self).read_data(filename, pointer)

        f = open(filename, "r+b")
        f.seek(self.pointer+3)
        self.wares = {}
        for menu in ["coin", "item", "weapon", "armor"]:
            self.wares[menu] = []
            if self.get_bit(menu):
                assert not self.get_bit("pawn")
                assert not self.get_bit("spell")
                while True:
                    value = read_multi(f, length=2)
                    if value == 0:
                        break
                    self.wares[menu].append(value)

        self.spells = []
        if self.get_bit("spell"):
            assert self.shop_type == 0x20
            while True:
                value = ord(f.read(1))
                if value == 0xFF:
                    break
                self.spells.append(value)

        f.close()

    def write_data(self, filename=None, pointer=None):
        super(ShopObject, self).write_data(filename, pointer)

        f = open(filename, "r+b")
        f.seek(self.pointer+3)
        for menu in ["coin", "item", "weapon", "armor"]:
            if self.get_bit(menu):
                assert self.wares[menu]
                assert not self.get_bit("pawn")
                assert not self.get_bit("spell")
                for value in self.wares[menu]:
                    write_multi(f, value, length=2)
                write_multi(f, 0, length=2)

        if self.get_bit("spell"):
            assert self.shop_type == 0x20
            assert self.spells
            for value in self.spells:
                f.write(chr(value))
            f.write("\xff")

        f.close()

    @classmethod
    def full_randomize(cls):
        ShopObject.class_reseed("full")
        shoppable_items = sorted(ShopObject.shoppable_items,
                                 key=lambda i: i.rank)
        coin_items = set([])
        for s in ShopObject.every:
            if s.wares["coin"]:
                coin_items |= set(s.wares_flat)
        shuffled_items = shuffle_normal(
            shoppable_items, random_degree=(get_random_degree() ** 0.5))
        new_coin_items = set([])
        for a, b in zip(shoppable_items, shuffled_items):
            if a in coin_items:
                new_coin_items.add(b)
        for i in (coin_items - new_coin_items):
            i.price = min(i.price * 2000, 65000)
        for i in (new_coin_items - coin_items):
            i.price = max(i.price / 2000, 1)
        non_coin_items = set(shoppable_items) - new_coin_items
        assert len(coin_items) == len(new_coin_items)

        for s in ShopObject.every:
            s.reseed(salt="mut")
            while True:
                badflag = False
                if s.wares_flat:
                    if s.wares["coin"]:
                        candidates = new_coin_items
                    else:
                        candidates = non_coin_items
                    if ((s.wares["weapon"] or s.wares["armor"])
                            and not s.wares["coin"]):
                        if not s.wares["weapon"]:
                            candidates = [c for c in candidates
                                          if not c.get_bit("weapon")
                                          or not c.get_bit("equipable")]
                        if not s.wares["armor"]:
                            candidates = [c for c in candidates
                                          if c.get_bit("weapon")
                                          or not c.get_bit("equipable")]
                        if not s.wares["item"]:
                            candidates = [c for c in candidates
                                          if c.get_bit("equipable")]

                    new_wares = ItemObject.get_similar_set(
                        s.wares_flat, candidates)
                    d = {}
                    d["weapon"] = [i for i in new_wares if i.get_bit("weapon")]
                    d["armor"] = [i for i in new_wares
                                  if i.get_bit("equipable")
                                  and i not in d["weapon"]]
                    d["item"] = [i for i in new_wares
                                 if i not in d["weapon"] + d["armor"]]

                    if ((s.wares["weapon"] or s.wares["armor"])
                            and not s.wares["coin"]):
                        for key in ["weapon", "armor", "item"]:
                            a = len(s.wares[key])
                            b = len(d[key])
                            if bool(a) != bool(b):
                                badflag = True
                                break
                    else:
                        d["item"].extend(d["weapon"])
                        d["item"].extend(d["armor"])
                        d["weapon"] = []
                        d["armor"] = []

                    if badflag:
                        continue
                    for key in ["weapon", "armor", "item"]:
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


if __name__ == "__main__":
    try:
        print ('You are using the Lufia II '
               'randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]
        run_interface(ALL_OBJECTS, snes=True, custom_degree=True)
        hexify = lambda x: "{0:0>2}".format("%x" % x)
        numify = lambda x: "{0: >3}".format(x)
        minmax = lambda x: (min(x), max(x))

        clean_and_write(ALL_OBJECTS)

        rewrite_snes_meta("L2-R", VERSION, lorom=True)
        finish_interface()
    except Exception, e:
        print "ERROR: %s" % e
        raw_input("Press Enter to close this program.")
