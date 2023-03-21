install:
	cd src ; make install
	cd VerifiedChecker ; make install

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
