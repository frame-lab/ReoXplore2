all:
	git submodule update --init
	make -C Reo2nuXmv
	make -C CACoq
