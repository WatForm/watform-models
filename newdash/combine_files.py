#!/usr/bin/python3

import os
import argparse
import pathlib


PROP_SUFFIX = '.ver'
# traces are <name>-traces.als
METHOD_SUFFIX = '-tcmc.als'
DEFAULT_DEST = 'combined-files'
DEST_FOLDER_NAME = 'combined-files'

#if not os.path.exists(destination):
#    os.makedirs(destination, exist_ok=True)

#sources = ['./2022-bandali-day', '2022-bandali-thesis', '2022-tamjid-thesis']

parser = argparse.ArgumentParser(
    description="Combines .als and .ver files to create .als files with property checks"
)

parser.add_argument('sources', nargs='*',
                    type=pathlib.Path,
                    default=['2022-bandali-day', '2022-bandali-thesis', '2019-serna-thesis', '2022-tamjid-thesis']
                    )
# parser.add_argument('-v', '--verbose', action='store_true')
parser.add_argument('-c', '--combine', action='store_true', help='combine the outputs of all sources.')

args = parser.parse_args()
sources = args.sources


for source in sources:
    print('Searching source:', source)
    all_fragments = []

    if args.combine:
        destination = DEFAULT_DEST
    else:
        destination = os.path.join(source, DEST_FOLDER_NAME)
    # create destination folder if it does not yet exist
    if not os.path.exists(destination):
       os.makedirs(destination, exist_ok=True)


    for root, dirs, files in os.walk(source):
        for file in files:
            fragment_path = str(os.path.join(root, file))
            all_fragments.append(fragment_path)

    traces = list(filter(lambda name: name.endswith(METHOD_SUFFIX), all_fragments))

    for trace in traces:
        print('Found trace:', trace)
        identifier = trace[:-len(METHOD_SUFFIX)]  # remove the suffix

        # Determine the name for the result file
        trace_path_split = trace.split('/')
        folder_name = trace_path_split[-2]
        file_name = trace_path_split[-1][:-len(METHOD_SUFFIX)]

        if folder_name.lower() == file_name.lower():
            model_name = folder_name
        else:
            model_name = folder_name + '-' + file_name

        print(f'Naming model "{model_name}"')

        # versions we care about will end with -tcmc-prop#.ver, and we will want the number
        prop_prefix = identifier + '-tcmc-prop'
        property_fragments = list(sorted(filter(
            lambda name: name.startswith(prop_prefix) and name.endswith(PROP_SUFFIX),
            all_fragments
        )))

        for property_fragment in property_fragments:
            property_number = property_fragment[len(prop_prefix):-len(PROP_SUFFIX)]
            print(f'  Found property number {property_number}')

            target_file_name = model_name + '-prop' + property_number + '.als'

            target_path = os.path.join(destination, target_file_name)

            print('    Writing to', target_path)
            with open(target_path, 'w') as target_file:
                with open(trace, 'r') as trace_file:
                    for line in trace_file:
                        target_file.write(line)

                target_file.write('/* P R O P E R T Y */\n')
                with open(property_fragment, 'r') as property_file:
                    for line in property_file:
                        target_file.write(line)

print('Done!')




