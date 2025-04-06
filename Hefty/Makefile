.PHONY: run clean test

ALL_SRCS := $(wildcard *.agda)
ALL_SRCS += $(wildcard Effect/*.agda)
ALL_SRCS += $(wildcard Effect/Core/*.agda)
ALL_SRCS += $(wildcard Effect/Free/*.agda)
ALL_SRCS += $(wildcard Effect/Free2/*.agda)
ALL_SRCS += $(wildcard Effect/Hefty/*.agda)
ALL_SRCS += $(wildcard Example/*.agda)
ALL_SRCS += $(wildcard Experimental/*.agda)
ALL_SRCS += $(wildcard Foundation/*.agda)
ALL_SRCS += $(wildcard Control/*.agda)
ALL_SRCS += $(wildcard Control/Effect/*.agda)
ALL_SRCS += $(wildcard Control/Effect/Algebraic/*.agda)
ALL_SRCS += $(wildcard Control/Effect/Algebraic/Effect/*.agda)
ALL_SRCS += $(wildcard Control/Effect/Algebraic/OpenUnion/*.agda)
ALL_SRCS += $(wildcard Control/Effect/Algebraic/FirstOrder/*.agda)

AGDA_CHECK := agda \
		--guardedness \
		--erasure \
		--erased-matches

test:
	for i in $(ALL_SRCS); do \
		${AGDA_CHECK} $$i; \
	done




#exports
run: Free2List
	./Free2List


15-IO: Experimental/15-IO.agda
	agda  -i. --compile  --library=standard-library-2.2 Experimental/15-IO.agda

Free2List: Example/Experimental/Free2List.agda
	agda  -i. --compile  --library=standard-library-2.2 Example/Experimental/Free2List.agda

runRep: Reproduce
	./Reproduce

Reproduce: MAlonzo
	ghc -O -o Reproduce \
		-Werror -i. \
		-main-is MAlonzo.Code.Example.Reproduce \
		MAlonzo/Code/Example/Reproduce.hs \
		--make -fwarn-incomplete-patterns




MAlonzo: Example/Reproduce.agda
	agda  -i. --ghc-dont-call-ghc --compile --library=standard-library-2.2 Example/Reproduce.agda

run1: build/jAgda.Example.IO.js
	NODE_PATH=./build node build/jAgda.Example.IO.js

IO: Example/IO.agda
	agda  -i. --compile  --library=standard-library-2.2 Example/IO.agda

build/jAgda.Example.IO.js: Example/IO.agda
	agda  -i. --js --compile-dir=build --library=standard-library-2.2 Example/IO.agda

Teletype: Example/Teletype.agda
	agda  -i. --compile --library=standard-library-2.2 Example/Teletype.agda

CustomOutHandler: Example/CustomOutHandler.agda
	agda  -i. --compile --library=standard-library-2.2 Example/CustomOutHandler.agda

clean:
	rm -rf Malonzo
	rm -rf Reproduce
	rm -rf dist-newstyle
	rm -rf *.agdai
	rm -rf Mystdlib/*.agdai
	rm -rf Example/*.agdai
	rm -rf Effect/*.agdai
	rm -rf Effect/Free/*.agdai
	rm -rf Effect/Hefty/*.agdai
	rm -f Hefty
	rm -f Teletype
	rm -f IO
	rm -f CustomOutHandler
	rm -f *.js
	rm -rf build
	rm -rf _build
	rm -f Free2List
