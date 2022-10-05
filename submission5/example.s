	.file	"example.c"
	.option nopic
	.text
	.align	1
	.globl	f
	.type	f, @function
f:
	addi	sp,sp,-16
	sd	s0,8(sp)
	addi	s0,sp,16
	li	a5,0
	mv	a0,a5
	ld	s0,8(sp)
	addi	sp,sp,16
	jr	ra
	.size	f, .-f
	.align	1
	.globl	publish
	.type	publish, @function
publish:
	addi	sp,sp,-32
	sd	s0,24(sp)
	addi	s0,sp,32
	mv	a5,a0
	sw	a5,-20(s0)
	nop
	ld	s0,24(sp)
	addi	sp,sp,32
	jr	ra
	.size	publish, .-publish
	.align	1
	.globl	main
	.type	main, @function
main:
	addi	sp,sp,-64
	sd	ra,56(sp)
	sd	s0,48(sp)
	addi	s0,sp,64
	mv	a5,a0
	sd	a1,-64(s0)
	sw	a5,-52(s0)
	ld	a5,-64(s0)
	lw	a5,4(a5)
	sw	a5,-20(s0)
	sw	zero,-40(s0)
	sw	zero,-36(s0)
	sw	zero,-32(s0)
	sw	zero,-28(s0)
	call	f
	mv	a5,a0
	sw	a5,-24(s0)
	lw	a5,-40(s0)
	mv	a4,a5
	li	a5,42
	bne	a4,a5,.L6
	lw	a5,-20(s0)
	mv	a0,a5
	call	publish
	j	.L5
.L6:
	lw	a5,-24(s0)
	mv	a0,a5
	call	publish
	nop
.L5:
	ld	ra,56(sp)
	ld	s0,48(sp)
	addi	sp,sp,64
	jr	ra
	.size	main, .-main
	.ident	"GCC: (g5964b5cd727) 11.1.0"
	.section	.note.GNU-stack,"",@progbits
