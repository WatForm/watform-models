DASHCLI=java -ea -cp /Users/nday/UW/github/org.alloytools.alloy/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar ca.uwaterloo.watform.dash4whole.Dash
TMP=tmp
# MODEL, METHOD need to be defined

all:
	cat $(MODEL).dsh $(METHOD)-properties.ver > $(TMP).dsh
	$(DASHCLI) -t -m $(METHOD) $(TMP).dsh
	mv $(TMP)-$(METHOD).als $(MODEL)-$(METHOD).als
	rm -rf $(TMP).dsh


clean:
	rm -rf *.als $(TMP)-*.* $(TMP).*