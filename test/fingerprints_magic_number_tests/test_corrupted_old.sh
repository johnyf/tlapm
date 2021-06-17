# First run the older version of `tlapm` twice,
# then corrupt the latest fingerprints file,
# then run the newer version of `tlapm`,
# which identifies the latest fingerprints file
# as corrupted, and renames it by appending `.corrupted`
# to the file name, and identifies also the older
# fingerprints file under the fingerprints history
# directory as from an old version, and does not load it.
PS4="> "
set -x
rm -rf .tlacache fingerprints_corrupted
cat Test.tla
tlapm_old Test.tla
tree .tlacache
tlapm_old Test.tla
tree .tlacache
echo "corrupted" > .tlacache/Test.tlaps/fingerprints
cp .tlacache/Test.tlaps/fingerprints fingerprints_corrupted
tlapm_new Test.tla
tree .tlacache
diff -s fingerprints_corrupted .tlacache/Test.tlaps/fingerprints.corrupted

