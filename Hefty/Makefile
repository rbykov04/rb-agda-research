.PHONY: run clean
run: Hefty
	./Hefty

Hefty: Hefty.agda
	agda  -i. --compile --library=standard-library-2.2 Hefty.agda

clean:
	rm -rf Malonzo
	rm -f Hefty
