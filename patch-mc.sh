file=$1
target='test.mc'
cp $file $target
sed -i '1imexpr' $target
perl -i -pe 'if (eof) { 
    if (/anon(\d+)/) { 
        $n=$1; $c=`cat input.mc`; $c =~ s/PLACEHOLDER/$n/g; $_=$c 
    } 
}' $target 
printf "g/^type Matrix/.,+1m/^type Mat /+1\nw\nq" | ed -s $target
