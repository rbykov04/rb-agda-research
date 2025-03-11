.PHONY: run clean

run: HelloWorld
	./HelloWorld

HelloWorld: Example/HelloWorld.agda
	agda  -i. --compile --library=standard-library-2.2 Example/HelloWorld.agda

clean:
	rm -rf Malonzo
	rm -rf dist-newstyle
	rm -rf *.agdai
	rm -rf Mystdlib/*.agdai
	rm -f Hefty
	rm -f HelloWorld
