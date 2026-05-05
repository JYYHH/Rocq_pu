
all: 
	rocq compile basic.v
	rocq compile Induction.v
	rocq compile Lists.v
	rocq compile Poly.v
	rocq compile Tactics.v
	rocq compile Logic.v
	rocq compile IndProp.v
	rocq compile Rel.v
	coqdoc *.v -d ./html
clean: 
	rm -f .*.aux *.vo *.glob *.vok *.vos html/*.html html/*.css hw/.*.aux hw/*.vo hw/*.glob hw/*.vok hw/*.vos hw/.lia.cache


