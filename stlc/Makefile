AGDA=agda

all: executable tests

executable:
	cd src/ && ${AGDA} --compile-dir=.. -c Main.agda

tests:
	./Main examples/silly.stlc
	./Main examples/swap2.stlc
	./Main examples/hid.stlc
