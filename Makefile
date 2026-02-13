
all: 
	rocq compile basic.v
	rocq compile Induction.v
	rocq compile Lists.v
	rocq compile Poly.v
	rocq compile Tactics.v
	rocq compile Logic.v
	rocq compile IndProp.v
clean: 
	rm .*.aux *.vo *.glob *.vok *.vos