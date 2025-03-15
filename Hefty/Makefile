.PHONY: run clean

#exports
run: Reproduce
	./Reproduce

Reproduce: Example/Reproduce.agda
	agda  -i. --compile --library=standard-library-2.2 Example/Reproduce.agda

run1: build/jAgda.Example.IO.js
	NODE_PATH=./build node build/jAgda.Example.IO.js


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
