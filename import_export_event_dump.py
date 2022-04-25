from randomizer import dump_events, patch_events, ALL_OBJECTS, MapEventObject
from randomtools.interface import run_interface
from os import remove, rename, path
from sys import argv
from time import time


if __name__ == '__main__':

    try:
        mode, sourcefile, script_dump = argv[1:]
        assert mode in ['import', 'export']
    except:
        print('USAGE:\n'
              'python3 import_export_event_dump.py import ROM_FILENAME EVENT_DUMP_TXT\n'
              'python3 import_export_event_dump.py export ROM_FILENAME EVENT_DUMP_TXT')
        exit(1)

    outfile = '_temp.smc'
    flags = ''
    seed = '0'
    args = [None, sourcefile, flags, seed]
    run_interface(ALL_OBJECTS, snes=False, args=args, setup_only=True,
                  override_outfile=outfile)

    for meo in MapEventObject.every:
        meo.preprocess()

    if mode == 'import':
        patch_events(script_dump)
        MapEventObject.write_all(outfile)
        backup_name = '{0}.backup'.format(sourcefile)
        if path.exists(backup_name):
            backup_name = '{0}.{1}'.format(backup_name, int(time()))
        rename(sourcefile, backup_name)
        rename(outfile, sourcefile)
    elif mode == 'export':
        dump_events(script_dump)
        remove(outfile)
