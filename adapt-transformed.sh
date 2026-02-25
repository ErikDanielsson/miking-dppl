rsimplestore='s/simpleStore/hrmStore/'
rsimpleinit='s/simpleInit/hrmInit/'

sed -e $rsimplestore -e $rsimpleinit $1 > $2
