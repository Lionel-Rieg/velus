# File generated by CompCert 3.5
# Command line: ok_multieq.lus
	.data
	.align	3
	.globl	_self$
_self$:
	.data
	.align	3
	.globl	_x$
_x$:
	.space	1
	.data
	.align	3
	.globl	_y$
_y$:
	.space	1
	.data
	.align	3
	.globl	_z$
_z$:
	.space	1
	.data
	.align	3
	.globl	_a$
_a$:
	.space	1
	.data
	.align	3
	.globl	_b$
_b$:
	.space	1
	.data
	.align	3
	.globl	_c$
_c$:
	.space	1
	.text
	.align	4
	.globl _fun$f$step
_fun$f$step:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %eax
	movl	%eax, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 8(%esp)
	movl	%edi, 12(%esp)
	movl	16(%eax), %edi
	movl	12(%eax), %esi
	movl	8(%eax), %edx
	movl	4(%eax), %ebx
	cmpl	$0, %edx
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 0(%ebx)
	cmpl	$0, %edx
	jne	L100
	xorl	%eax, %eax
	movb	%al, 2(%ebx)
	jmp	L101
L100:
	cmpl	$0, %edi
	setne	%dl
	movzbl	%dl, %edx
	movb	%dl, 2(%ebx)
L101:
	movzbl	0(%ebx), %edx
	cmpl	$0, %edx
	jne	L102
	xorl	%eax, %eax
	movb	%al, 1(%ebx)
	jmp	L103
L102:
	cmpl	$0, %esi
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 1(%ebx)
L103:
	movl	4(%esp), %ebx
	movl	8(%esp), %esi
	movl	12(%esp), %edi
	addl	$28, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$f$reset
_fun$f$reset:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %eax
	movl	%eax, 0(%esp)
	addl	$12, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _main_proved
_main_proved:
	.cfi_startproc
	subl	$44, %esp
	.cfi_adjust_cfa_offset	44
	leal	48(%esp), %eax
	movl	%eax, 20(%esp)
	movl	%ebx, 24(%esp)
	movl	%esi, 28(%esp)
	movl	%edi, 32(%esp)
	movl	%ebp, 36(%esp)
	leal	_self$, %ecx
	movl	%ecx, 0(%esp)
	call	_fun$f$reset
L104:
	movzbl	_a$, %eax
	movzbl	_b$, %ebx
	movzbl	_c$, %ebp
	leal	_self$, %edi
	leal	40(%esp), %edx
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %esi
	cmpl	$0, %ebx
	setne	%bl
	movzbl	%bl, %ebx
	cmpl	$0, %ebp
	setne	%al
	movzbl	%al, %eax
	movl	%eax, 16(%esp)
	movl	%ebx, 12(%esp)
	movl	%esi, 8(%esp)
	movl	%edx, 4(%esp)
	movl	%edi, 0(%esp)
	call	_fun$f$step
	movzbl	40(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _x$
	movzbl	41(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _y$
	movzbl	42(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _z$
	jmp	L104
	.cfi_endproc
	.text
	.align	4
	.globl _main
_main:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %eax
	movl	%eax, 0(%esp)
	call	_main_proved
	movl	%ebx, %eax
	addl	$12, %esp
	ret
	.cfi_endproc
	.section __IMPORT,__pointers,non_lazy_symbol_pointers