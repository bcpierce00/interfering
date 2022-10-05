	.file	"reference.c"
	.option nopic
	.text
	.align	1
	.globl	f
	.type	f, @function
f:
	addi	sp,sp,-32
	sd	s0,24(sp)
	addi	s0,sp,32
	sw	a0,-24(s0)
	li	a5,0
	mv	a0,a5
	ld	s0,24(sp)
	addi	sp,sp,32
	jr	ra
	.size	f, .-f
	.align	1
	.globl	main
	.type	main, @function
main:
	addi	sp,sp,-32
	sd	ra,24(sp)
	sd	s0,16(sp)
	addi	s0,sp,32
	sw	zero,-24(s0)
	lw	a5,-24(s0)
	mv	a0,a5
	call	f
	nop
	ld	ra,24(sp)
	ld	s0,16(sp)
	addi	sp,sp,32
	jr	ra
	.size	main, .-main
	.ident	"GCC: (g5964b5cd727) 11.1.0"
	.section	.note.GNU-stack,"",@progbits
