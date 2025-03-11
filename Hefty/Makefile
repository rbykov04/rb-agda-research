.PHONY: run clean

run: CustomOutHandler
	./CustomOutHandler


Teletype: Example/Teletype.agda
	agda  -i. --compile --library=standard-library-2.2 Example/Teletype.agda

CustomOutHandler: Example/CustomOutHandler.agda
	agda  -i. --compile --library=standard-library-2.2 Example/CustomOutHandler.agda

clean:
	rm -rf Malonzo
	rm -rf dist-newstyle
	rm -rf *.agdai
	rm -rf Mystdlib/*.agdai
	rm -rf Example/*.agdai
	rm -rf Effect/*.agdai
	rm -rf Effect/Free/*.agdai
	rm -rf Effect/Hefty/*.agdai
	rm -f Hefty
	rm -f Teletype
	rm -f CustomOutHandler
