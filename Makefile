
core_flags = -dsuppress-coercions -ddump-simpl -dsuppress-idinfo \
						 -dsuppress-type-applications -dsuppress-uniques \
						 -dsuppress-module-prefixes -ddump-to-file

prof_flags = -prof -fprof-auto

default:
	ghc --make -O3 Turing.hs $(core_flags)

prof:
	ghc --make -O3 Turing.hs -o Turing_p $(prof_flags)
