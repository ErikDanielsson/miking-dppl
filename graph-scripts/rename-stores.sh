rsimplestore='s/simpleStore/hrmStore/'
rsimpleinit='s/simpleInit/hrmInit/'
transformed_copy=$1
target=$2
sed -e $rsimplestore -e $rsimpleinit $transformed_copy > $target
