# First create a fingerprints file with an older version
# of `tlapm`, then the newer version of `tlapm` renames the
# fingerprints file by appending `.old` to the filename.
PS4="> "
set -x
rm -rf .tlacache fingerprints_old
cat Test.tla
tlapm_old Test.tla
tree .tlacache
cp .tlacache/Test.tlaps/fingerprints fingerprints_old
tlapm_new Test.tla
tree .tlacache
diff -s fingerprints_old .tlacache/Test.tlaps/fingerprints.old

