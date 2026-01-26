#!/usr/bin/env fish
echo $1
and sed -e "/{{HERE}}/{r $argv[1]" -e "d}" \
  hrm-template.mc > build/full-temp.mc
and echo fixing complete, compiling model
and mi compile build/full-temp.mc --output build/full-temp
and echo compilation complete, running
and time build/full-temp
and echo running complete, done
