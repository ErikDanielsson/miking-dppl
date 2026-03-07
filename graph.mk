%.test.mc : %.mc
	graph-scripts/patch-printed-mc.sh $< $$(dirname $<)/input.mc $@

# Run the transformation (always keep this file)
.PRECIOUS: %.transformed.mc
%.transformed.mc : %.test.mc
	# We have to copy the file to test.mc to be 
	# compatible with the transformation binary
	cp $< test.mc
	graph-scripts/transform.fish $@

# Use the simple interface for testing
%.full-simple.mc : %.transformed.mc
	sed -e "/{{HERE}}/{r $<" -e "d}" \
	test-template.mc > $@

# Create a file to be edited with the HRM
# interface. When we want to make the file 
%.renamed-HRM.mc : %.transformed.mc
	graph-scripts/rename-stores.sh $< $@

# Use the HRM interface for inference
%.full-HRM.mc : %.edit-HRM.mc %.renamed-HRM.mc hrm-template.mc
	- diff -u $*.edit-HRM.mc $*.renamed-HRM.mc > $*.HRM.diff
	sed -e "/{{HERE}}/{r $<" -e "d}" \
	hrm-template.mc > $@


%.out : %.mc
	mi compile $< --output $@
