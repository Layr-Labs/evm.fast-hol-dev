#!/usr/bin/env python3
"""Shorten author articles by releasing dictionary objects at their last use.

This only rewrites the writer's immediate-number def/ref/remove commands.
The result is untrusted proof data and must still pass independent HOL replay.
"""
import argparse
from pathlib import Path


def compact(source, destination):
    source, destination = Path(source), Path(destination)
    if source.resolve() == destination.resolve():
        raise ValueError('input and output must differ')
    active, drops, replacements = {}, set(), set()
    lifetimes = 0
    def finish(entry):
        nonlocal lifetimes
        lifetimes += 1
        definition, last_use = entry
        if definition == last_use:
            drops.update((definition-1, definition))
        else:
            replacements.add(last_use)
    previous, removal = b'', None
    with source.open('rb') as stream:
        for number, line in enumerate(stream, 1):
            command = line.strip()
            if removal is not None:
                if command == b'pop':
                    finish(removal)
                    drops.update((number-2, number-1, number))
                removal = None
            if command in (b'def', b'ref', b'remove'):
                if not previous.strip().isdigit():
                    raise ValueError(f'non-immediate dictionary operand at line {number}')
                key = int(previous.strip())
                if command == b'def':
                    if key in active:
                        finish(active[key])
                    active[key] = (number, number)
                elif key not in active:
                    raise ValueError(f'unknown dictionary key {key} at line {number}')
                elif command == b'remove':
                    removal = active.pop(key)
                else:
                    active[key] = (active[key][0], number)
            previous = line
    for entry in active.values():
        finish(entry)
    with source.open('rb') as stream, destination.open('wb') as output:
        for number, line in enumerate(stream, 1):
            if number not in drops:
                output.write(b'remove\n' if number in replacements else line)
    return lifetimes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    count = compact(args.source, args.destination)
    print(f'Compacted {count} dictionary lifetimes: '
          f'{args.source.stat().st_size} -> {args.destination.stat().st_size} bytes')


if __name__ == '__main__':
    main()
