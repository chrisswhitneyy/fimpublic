CC=ghc -O2

all : 
	$(CC) -iInt:../../Extraction/Haskell/Int -cpp -DNATIVE --make fim_run.hs -o fim_int_run
	$(CC) -iInteger:../../Extraction/Haskell/Integer -cpp -DNATIVE --make fim_run.hs -o fim_integer_run
	$(CC) -i../../Extraction/Haskell/Basic -cpp --make fim_run.hs -o fim_basic_run

clean :
	rm -f *.hi fim_*_run
