
FLAG := -R VCT VCT -R Coq-dL CoqDL -R Coq-dL/coq-tools CoqDL.util -R Coq-dL/syntax CoqDL.syntax -R Coq-dL/semantics CoqDL.semantics -R Coq-dL/substitution CoqDL.substitution -R Coq-dL/axioms CoqDL.axioms -R Coq-dL/checker CoqDL.checker -R Coq-dL/examples CoqDL.examples

AbstractPrograms.vo : AbstractPrograms.v DifferentialContracts.vo
	coqc ${FLAG} AbstractPrograms.v

DifferentialContracts.vo: DifferentialContracts.v Coq-dL/all.vo VCT/all.vo
	coqc ${FLAG} DifferentialContracts.v

Coq-dL/all.vo:
	cd Coq-dL && $(MAKE)

VCT/all.vo:
	cd VCT && $(MAKE)

clean:
	rm -f .*.aux *.vo *.glob

clean-CoqDL:
	cd Coq-dL && $(MAKE) clean

clean-VCT:
	cd VCT && $(MAKE) clean

clean-all:
	rm -f .*.aux *.vo *.glob
	cd Coq-dL && $(MAKE) clean
	cd VCT && $(MAKE) clean
