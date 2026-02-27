rsimplestore='s/simpleStore/hrmStore/'
rsimpleinit='s/simpleInit/hrmInit/'
target=$2
transformed_copy=$1
sed -e $rsimplestore -e $rsimpleinit $transformed_copy > $target
