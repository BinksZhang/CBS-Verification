-include CONFIGURE
COQMFFLAGS := -Q . SLF 

ALLVFILES := TLC/LibAxioms.v TLC/LibTactics.v TLC/LibEqual.v TLC/LibLogic.v TLC/LibOperation.v TLC/LibBool.v \
 TLC/LibReflect.v TLC/LibProd.v TLC/LibSum.v TLC/LibRelation.v TLC/LibOrder.v TLC/LibNat.v TLC/LibEpsilon.v TLC/LibInt.v \
  TLC/LibMonoid.v TLC/LibContainer.v TLC/LibOption.v TLC/LibWf.v TLC/LibList.v TLC/LibListZ.v TLC/LibMin.v TLC/LibSet.v \
  TLC/LibChoice.v TLC/LibUnit.v TLC/LibFun.v TLC/LibString.v TLC/LibMultiset.v TLC/LibCore.v TLC/TLCbuffer.v \
	Fmap.v Var.v Language.v InnerPre.v Himpl.v Rules.v ExBasic.v Example.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

cleantlc:
	cd ./TLC && $(MAKE)

clean:
	rm -rf *.vo
	rm -rf .*.aux
	rm -rf *.aux
	rm -rf *.glob
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: build clean
