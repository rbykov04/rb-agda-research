.PHONY: run clean

run: CustomOutHandler
	./CustomOutHandler

CustomOutHandler: Example/CustomOutHandler.agda
	agda  -i. --compile --library=standard-library-2.2 Example/CustomOutHandler.agda

clean:
	rm -rf Malonzo
	rm -rf dist-newstyle
	rm -rf *.agdai
	rm -rf Mystdlib/*.agdai
	rm -f Hefty
	rm -f CustomOutHandler
