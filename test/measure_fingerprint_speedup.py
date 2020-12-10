#!/usr/bin/env python
"""Measure the run time difference before and after fingerprinting."""
import argparse
import matplotlib.pyplot as plt
import os
import pickle
import subprocess
import time


CACHE_DIR = '__tlacache__'
PICKLE_FILE = 'runtimes_after.pickle'
IMG_FILE = 'runtimes_after.png'


def main(measure):
    if measure:
        measure_timings()
    runtimes = load_measurements(PICKLE_FILE)
    plot_measurements(runtimes)
    for name, (a, b) in runtimes.items():
        if a < 1:
            continue
        print(name, a, b)


def measure_timings():
    print('listing files in directory and subdirectories')
    test_files = list_test_files()
    print('{n} test files found'.format(n=len(test_files)))
    print('\n'.join(test_files))
    dir_paths = [os.path.dirname(path) for path in test_files]
    for a, b in zip(test_files, dir_paths):
        print(a)
        print(b)
    runtimes = run_tlapm_on_files(test_files)
    dump_runtimes(runtimes, filename=PICKLE_FILE)


def list_test_files():
    test_files = list()
    root = '.'
    for path, subdirs, files in os.walk(root):
        if CACHE_DIR in path:
            continue
        for name in files:
            base, ext = os.path.splitext(name)
            if ext != '.tla':
                continue
            # comment this `if` statement in order to
            # use this script with the `examples/`
            # directory of the `tlapm` repository
            if not base.endswith('_test'):
                continue
            file_path = os.path.join(path, name)
            test_files.append(file_path)
    return test_files


def run_tlapm_on_files(file_paths):
    runtimes = dict()
    for file_path in file_paths:
        print('running: `{f}`'.format(f=file_path))
        dt = run_tlapm(file_path)
        dt_with_fingerprints = run_tlapm(file_path)
        runtimes[file_path] = (dt, dt_with_fingerprints)
    return runtimes


def run_tlapm(file_path):
    directory = os.path.dirname(file_path)
    file_name = os.path.basename(file_path)
    cmd = ['tlapm', file_name]
    t1 = time.time()
    process = subprocess.run(cmd, cwd=directory)
    t2 = time.time()
    print('return code: {c}'.format(c=process.returncode))
    dt = t2 - t1
    return dt


def make_comparison_plots(filename_before, filename_after, comparison_img):
    runtimes_before = load_measurements(filename_before)
    runtimes_after = load_measurements(filename_after)
    plot_comparison(runtimes_before, runtimes_after, comparison_img)


def plot_measurements(runtimes):
    # x[1][0] is the runtime without fingerprints
    data = sorted(runtimes.items(), key=lambda x: x[1][0])
    # u[1][0] is the runtime without fingerprints
    xy = [(i, u[1][0]) for i, u in enumerate(data)]
    xs = [u[0] for u in xy]
    ys = [u[1] for u in xy]
    plt.plot(xs, ys, 'r-', label='without fingerprints')
    # u[1][1] is the runtime with fingerprints present
    xy = [(i, u[1][1]) for i, u in enumerate(data)]
    xs = [u[0] for u in xy]
    ys = [u[1] for u in xy]
    plt.plot(xs, ys, 'b--', label='with fingerprints')
    # title, axis labels
    plt.title('Running time with and without fingerprints')
    plt.xlabel('Test file')
    plt.ylabel('Running time (sec)')
    plt.yscale('log')
    plt.legend()
    # dump to file
    plt.savefig(IMG_FILE)


def plot_comparison(runtimes_before, runtimes_after, comparison_img):
    data_before = sorted(runtimes_before.items(), key=lambda x: x[1][0])
    names = [u[0] for u in data_before]
    data_after = [(name, runtimes_after[name]) for name in names]
    t1_before = [u[1][0] for u in data_before]
    t2_before = [u[1][1] for u in data_before]
    t1_after = [u[1][0] for u in data_after]
    t2_after = [u[1][1] for u in data_after]
    n = len(data_before)
    x = list(range(n))
    #
    # before
    # plot the speedup of without fingerprints and with fingerprints
    speedup_before = [t1_before[i] / t2_before[i] for i in range(n)]
    #
    # after
    # plot the speedup of without fingerprints and with fingerprints
    speedup_after = [t1_after[i] / t2_after[i] for i in range(n)]
    #
    # comparison before to after
    # plot the speedup without fingerprints
    speedup_wo = [t1_before[i] / t1_after[i] for i in range(n)]
    #
    # plot the speedup with fingerprints
    speedup_with = [t2_before[i] / t2_after[i] for i in range(n)]
    #
    # plot the above
    fig, (ax1, ax2, ax3, ax4, ax5) = plt.subplots(
        5, sharex=True, figsize=(20, 10))
    fig.tight_layout(pad=4.0)
    fig.suptitle('Speedup measurements')
    #
    ax1.plot(x, speedup_before)
    ax1.set_title('Ratio without / with fingerprints before change')
    ax1.set(xlabel='TLA+ file', ylabel='Ratio of times')
    ax1.grid()
    #
    ax2.plot(x, speedup_after)
    ax2.set_title('Ratio without / with fingerprints after change')
    ax2.set(xlabel='TLA+ file', ylabel='Ratio of times')
    ax2.grid()
    #
    ax3.plot(x, speedup_wo)
    ax3.set_title('Ratio before / after, without fingerprints')
    ax3.set(xlabel='TLA+ file', ylabel='Ratio of times')
    ax3.grid()
    #
    ax4.plot(x, speedup_with)
    ax4.set_title('Ratio before / after, with fingerprints')
    ax4.set(xlabel='TLA+ file', ylabel='Ratio of times')
    ax4.grid()
    #
    ax5.plot(x, t1_before)
    ax5.set_title('Running time before change, without fingerprints')
    ax5.set(xlabel='TLA+ file', ylabel='Time (sec)')
    ax5.set_yscale('log')
    ax5.grid()
    # dump to file
    plt.savefig(comparison_img)


def dump_runtimes(runtimes, filename):
    with open(filename, 'wb') as f:
        pickle.dump(runtimes, f)


def load_measurements(filename):
    with open(filename, 'rb') as f:
        runtimes = pickle.load(f)
    return runtimes


def _parse_args():
    parser = argparse.ArgumentParser(
        description='Measure `tlapm` timing before and after fingerprints')
    parser.add_argument('--measure', action='store_true',
        help='run tests and measure `tlapm` runtimes')
    args = parser.parse_args()
    return args.measure


if __name__ == '__main__':
    measure = _parse_args()
    main(measure)
    #
    # comparison
    # filename_before = 'runtimes_old.pickle'
    # filename_after = 'runtimes.pickle'
    # comparison_img = 'comparison.png'
    # make_comparison_plots(filename_before, filename_after, comparison_img)
