cppl_file=$1
# convert the file to test.mc, inserting input from input.mc
./patch-mc.sh $cppl_file
# Run Viktor's translation, result in build/transformed.mc
./mktest.fish
