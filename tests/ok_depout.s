# File generated by CompCert 3.5
# Command line: ok_depout.lus
	.data
	.align	3
	.globl	_self$
_self$:
	.space	1
	.data
	.align	3
	.globl	_x$
_x$:
	.space	1
	.data
	.align	3
	.globl	_b$
_b$:
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
	movl	8(%eax), %edi
	movl	4(%eax), %ebx
	movl	0(%eax), %esi
	movzbl	0(%esi), %ecx
	cmpl	$0, %ecx
	setne	%al
	movzbl	%al, %eax
	movb	%al, 0(%ebx)
	cmpl	$0, %edi
	setne	%al
	movzbl	%al, %eax
	movb	%al, 0(%esi)
	movzbl	0(%ebx), %edx
	cmpl	$0, %edx
	jne	L100
	xorl	%eax, %eax
	movb	%al, 1(%ebx)
	jmp	L101
L100:
	movl	$1, %ecx
	movb	%cl, 1(%ebx)
L101:
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
	movl	0(%eax), %ecx
	xorl	%edx, %edx
	movb	%dl, 0(%ecx)
	addl	$12, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$main$step
_fun$main$step:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %eax
	movl	%eax, 12(%esp)
	movl	%ebx, 16(%esp)
	movl	%esi, 20(%esp)
	movl	4(%eax), %edx
	movl	0(%eax), %esi
	leal	24(%esp), %ebx
	cmpl	$0, %edx
	setne	%dl
	movzbl	%dl, %edx
	movl	%edx, 8(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 0(%esp)
	call	_fun$f$step
	movzbl	24(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movl	16(%esp), %ebx
	movl	20(%esp), %esi
	addl	$28, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$main$reset
_fun$main$reset:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %eax
	movl	%eax, 4(%esp)
	movl	0(%eax), %ecx
	movl	%ecx, 0(%esp)
	call	_fun$f$reset
	addl	$12, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _main_proved
_main_proved:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %eax
	movl	%eax, 8(%esp)
	leal	_self$, %ecx
	movl	%ecx, 0(%esp)
	call	_fun$main$reset
L102:
	movzbl	_b$, %eax
	leal	_self$, %edx
	cmpl	$0, %eax
	setne	%cl
	movzbl	%cl, %ecx
	movl	%ecx, 4(%esp)
	movl	%edx, 0(%esp)
	call	_fun$main$step
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _x$
	jmp	L102
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