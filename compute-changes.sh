wip_dir="WIP"
work_file=$1
orig_file='build/transformed-model.mc'
patch_file=WIP/work-done.diff

diff -Nu $orig_file $work_file > $patch_file
