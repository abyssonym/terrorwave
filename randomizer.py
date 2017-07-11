from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses,
    mutate_normal, shuffle_normal)
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
RESEED_COUNTER = 0


def reseed():
    global RESEED_COUNTER
    RESEED_COUNTER += 1
    seed = get_seed()
    random.seed(seed + (RESEED_COUNTER**2))


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


class CapsuleObject(TableObject):
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


class SpellObject(TableObject):
    @property
    def name(self):
        return self.name_text.strip()


class CharacterObject(TableObject):
    @property
    def name(self):
        return self.name_text.strip()


class MonsterObject(TableObject):
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
        assert self.level * self.hp * self.xp != 0
        self._rank = self.level * self.hp * self.xp
        return self.rank

    @classmethod
    def intershuffle(cls):
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


class ItemObject(AdditionalPropertiesMixin, TableObject):
    additional_bitnames = ['misc1', 'misc2']

    @property
    def name(self):
        return ItemNameObject.get(self.index).name_text.strip()

    @property
    def rank(self):
        if hasattr(self, "_rank"):
            return self._rank

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

            0x1a6: 100 * 2000
        }
        if self.index in rankdict:
            self._rank = rankdict[self.index]
        elif 0x18e <= self.index <= 0x19b:
            self._rank = self.price * 2000
        elif self.price <= 2 or self.get_bit("unsellable"):
            self._rank = -1
        else:
            self._rank = self.price
        return self.rank


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
