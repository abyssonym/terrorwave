from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses)
from randomtools.utils import (
    classproperty, mutate_normal, shuffle_bits, get_snes_palette_transformer,
    write_multi, utilrandom as random)
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


class ItemObject(TableObject):
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
