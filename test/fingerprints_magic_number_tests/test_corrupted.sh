# Test `tlapm` behavior when the latest fingerprints file
# is corrupted. First run the old version of `tlapm`,
# then corrupt the (latest and only) fingerprints file,
# and then run the newer version of `tlapm`,
# which renames the corrupted fingerprints file,
# by appending `.corrupted` to the filename.
PS4="> "
set -x
rm -rf .tlacache fingerprints_corrupted
cat Test.tla
tlapm_old Test.tla
tree .tlacache
echo "corrupted" > .tlacache/Test.tlaps/fingerprints
cp .tlacache/Test.tlaps/fingerprints fingerprints_corrupted
tlapm_new Test.tla
tree .tlacache
diff -s fingerprints_corrupted .tlacache/Test.tlaps/fingerprints.corrupted

