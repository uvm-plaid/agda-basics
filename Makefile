V = 002

.PHONY: run
run: MAlonzo/Code/Basics$V.agda
	stack runghc --package ieee MAlonzo/Code/Basics001.hs 

MAlonzo/Code/Basics$V.agda: Basics$V.agda
	stack exec --package ieee --package random -- agda --compile Basics$V.agda

.PHONY: clean
clean:
	rm -rf MAlonzo
