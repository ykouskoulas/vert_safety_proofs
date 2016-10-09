all : vert.vo seot_util.vo analysis.vo

analysis.vo: analysis.v
	coqc analysis.v

seot_util.vo : seot_util.v
	coqc seot_util.v

vert.vo : vert.v seot_util.vo analysis.vo
	coqc vert.v

clean :
	rm *.vo *.glob
