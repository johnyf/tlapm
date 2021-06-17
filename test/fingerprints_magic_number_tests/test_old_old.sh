# First run the older version of `tlapm` twice,
# which creates both an old fingerprints file and
# a fingerprints file under the directory of
# fingerprints history.
#
# Then run the newer version of `tlapm`, which tries
# to load both existing fingerprints files,
# identifies them as old, and renames one of them
# by appending `.old` to the filename.
PS4="> "
set -x
rm -rf .tlacache fingerprints_old
cat Test.tla
tlapm_old Test.tla
tree .tlacache
tlapm_old Test.tla
tree .tlacache
cp .tlacache/Test.tlaps/fingerprints fingerprints_old
tlapm_new Test.tla
tree .tlacache
diff -s fingerprints_old .tlacache/Test.tlaps/fingerprints.old

