This directory contains scripts that test how `tlapm`
behaves when there already exist fingerprints files
from a previous version of `tlapm` that had a different
"magic number" in the fingerprints file.

There are tests also for the behavior of `tlapm` in
the presence of a corrupted fingerprints file.

Running the test scripts of this directory requires
installing two versions of `tlapm` that are present
in the `PATH` and named as:
- `tlapm_old`
- `tlapm_new`
