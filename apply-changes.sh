wip_dir="WIP"
new_orig_file=$1
new_work_file=new-host-rep-inference.mc
orig_file='build/transformed-model.mc'
patch_file=WIP/work-done.diff

cp $orig_file $new_orig_file
patch $new_orig_file $patch_file