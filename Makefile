install:
	cd src ; make install

linstall:
	cd VerifiedChecker ; make install

ptest:
	cd test ; make test

ltest:
	cd test ; make ltest


run:
	cd benchmarks ; make run

lrun:
	cd benchmarks ; make lrun

clean:
	rm -f *~
	cd benchmarks; make clean
	cd src ; make clean
	cd test ; make clean
	cd tools ; make clean

superclean:
	rm -f *~
	cd benchmarks; make superclean
	cd src ; make superclean
	cd test ; make superclean
	cd tools ; make superclean
