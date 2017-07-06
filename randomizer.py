from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses)
from randomtools.utils import (
    classproperty, mutate_normal, shuffle_bits, get_snes_palette_transformer,
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
    @property
    def name(self):
        return self.name_text.strip()


class ChestObject(TableObject):
    @property
    def item_index(self):
        return (
            self.get_bit("item_high_bit") << 8) | self.item_low_byte

    @property
    def item(self):
        return ItemObject.get(self.item_index)


class SpellObject(TableObject):
    @property
    def name(self):
        return self.name_text.strip()


class CharacterObject(TableObject):
    @property
    def name(self):
        return self.name_text.strip()


class MonsterObject(TableObject):
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


class ItemObject(AdditionalPropertiesMixin, TableObject):
    additional_bitnames = ['misc1', 'misc2']

    @property
    def name(self):
        return ItemNameObject.get(self.index).name_text.strip()


class ItemNameObject(TableObject): pass


if __name__ == "__main__":
    try:
        print ('You are using the Lufia II '
               'randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]
        run_interface(ALL_OBJECTS, snes=True)
        hexify = lambda x: "{0:0>2}".format("%x" % x)
        numify = lambda x: "{0: >3}".format(x)
        minmax = lambda x: (min(x), max(x))

        clean_and_write(ALL_OBJECTS)

        rewrite_snes_meta("L2-R", VERSION, lorom=True)
        finish_interface()
    except Exception, e:
        print "ERROR: %s" % e
        raw_input("Press Enter to close this program.")
