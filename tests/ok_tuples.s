# File generated by CompCert 3.5
# Command line: ok_tuples.lus
	.data
	.align	3
	.globl	_self$
_self$:
	.space	2
	.data
	.align	3
	.globl	_w$
_w$:
	.space	1
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
	.data
	.align	3
	.globl	_d$
_d$:
	.space	1
	.text
	.align	4
	.globl _fun$swap$step
_fun$swap$step:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %eax
	movl	%eax, 0(%esp)
	movl	%ebx, 4(%esp)
	movl	%esi, 8(%esp)
	movl	%edi, 12(%esp)
	movl	12(%eax), %esi
	movl	8(%eax), %edi
	movl	4(%eax), %edx
	movl	0(%eax), %ebx
	movzbl	0(%ebx), %ecx
	cmpl	$0, %ecx
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 0(%edx)
	cmpl	$0, %edi
	setne	%al
	movzbl	%al, %eax
	movb	%al, 1(%edx)
	cmpl	$0, %esi
	setne	%dl
	movzbl	%dl, %edx
	movb	%dl, 0(%ebx)
	movl	4(%esp), %ebx
	movl	8(%esp), %esi
	movl	12(%esp), %edi
	addl	$28, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$swap$reset
_fun$swap$reset:
	.cfi_startproc
	subl	$12, %esp
	.cfi_adjust_cfa_offset	12
	leal	16(%esp), %eax
	movl	%eax, 0(%esp)
	movl	0(%eax), %ecx
	movl	$1, %edx
	movb	%dl, 0(%ecx)
	addl	$12, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$shuffle$step
_fun$shuffle$step:
	.cfi_startproc
	subl	$60, %esp
	.cfi_adjust_cfa_offset	60
	leal	64(%esp), %eax
	movl	%eax, 16(%esp)
	movl	%ebx, 20(%esp)
	movl	%esi, 24(%esp)
	movl	%edi, 28(%esp)
	movl	%ebp, 32(%esp)
	movl	20(%eax), %eax
	movl	%eax, 40(%esp)
	movl	16(%esp), %eax
	movl	16(%eax), %eax
	movl	%eax, 44(%esp)
	movl	16(%esp), %eax
	movl	12(%eax), %edx
	movl	8(%eax), %ecx
	movl	4(%eax), %ebx
	movl	0(%eax), %esi
	leal	50(%esp), %ebp
	cmpl	$0, %ecx
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %edi
	cmpl	$0, %edx
	setne	%al
	movzbl	%al, %eax
	movl	%eax, 12(%esp)
	movl	%edi, 8(%esp)
	movl	%ebp, 4(%esp)
	movl	%esi, 0(%esp)
	call	_fun$swap$step
	movzbl	50(%esp), %edx
	cmpl	$0, %edx
	setne	%al
	movzbl	%al, %eax
	movb	%al, 0(%ebx)
	movzbl	51(%esp), %eax
	cmpl	$0, %eax
	setne	%dl
	movzbl	%dl, %edx
	movb	%dl, 1(%ebx)
	leal	1(%esi), %edx
	leal	48(%esp), %esi
	movl	44(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %edi
	movl	40(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movl	%eax, 12(%esp)
	movl	%edi, 8(%esp)
	movl	%esi, 4(%esp)
	movl	%edx, 0(%esp)
	call	_fun$swap$step
	movzbl	48(%esp), %ecx
	cmpl	$0, %ecx
	setne	%dl
	movzbl	%dl, %edx
	movb	%dl, 2(%ebx)
	movzbl	49(%esp), %ecx
	cmpl	$0, %ecx
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 3(%ebx)
	movl	20(%esp), %ebx
	movl	24(%esp), %esi
	movl	28(%esp), %edi
	movl	32(%esp), %ebp
	addl	$60, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$shuffle$reset
_fun$shuffle$reset:
	.cfi_startproc
	subl	$28, %esp
	.cfi_adjust_cfa_offset	28
	leal	32(%esp), %eax
	movl	%eax, 4(%esp)
	movl	%ebx, 8(%esp)
	movl	0(%eax), %ebx
	movl	%ebx, 0(%esp)
	call	_fun$swap$reset
	leal	1(%ebx), %eax
	movl	%eax, 0(%esp)
	call	_fun$swap$reset
	movl	8(%esp), %ebx
	addl	$28, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _fun$main$step
_fun$main$step:
	.cfi_startproc
	subl	$60, %esp
	.cfi_adjust_cfa_offset	60
	leal	64(%esp), %eax
	movl	%eax, 24(%esp)
	movl	%ebx, 28(%esp)
	movl	%esi, 32(%esp)
	movl	%edi, 36(%esp)
	movl	%ebp, 40(%esp)
	movl	20(%eax), %eax
	movl	%eax, 48(%esp)
	movl	24(%esp), %eax
	movl	16(%eax), %edx
	movl	12(%eax), %esi
	movl	8(%eax), %ecx
	movl	4(%eax), %ebx
	movl	0(%eax), %eax
	movl	%eax, 52(%esp)
	leal	56(%esp), %edi
	cmpl	$0, %ecx
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %ebp
	cmpl	$0, %edx
	setne	%dl
	movzbl	%dl, %edx
	cmpl	$0, %esi
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %esi
	movl	48(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movl	%eax, 20(%esp)
	movl	%esi, 16(%esp)
	movl	%edx, 12(%esp)
	movl	%ebp, 8(%esp)
	movl	%edi, 4(%esp)
	movl	52(%esp), %ecx
	movl	%ecx, 0(%esp)
	call	_fun$shuffle$step
	movzbl	56(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, 0(%ebx)
	movzbl	57(%esp), %edx
	cmpl	$0, %edx
	setne	%al
	movzbl	%al, %eax
	movb	%al, 1(%ebx)
	movzbl	58(%esp), %edx
	cmpl	$0, %edx
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 2(%ebx)
	movzbl	59(%esp), %edx
	cmpl	$0, %edx
	setne	%cl
	movzbl	%cl, %ecx
	movb	%cl, 3(%ebx)
	movl	28(%esp), %ebx
	movl	32(%esp), %esi
	movl	36(%esp), %edi
	movl	40(%esp), %ebp
	addl	$60, %esp
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
	call	_fun$shuffle$reset
	addl	$12, %esp
	ret
	.cfi_endproc
	.text
	.align	4
	.globl _main_proved
_main_proved:
	.cfi_startproc
	subl	$60, %esp
	.cfi_adjust_cfa_offset	60
	leal	64(%esp), %eax
	movl	%eax, 24(%esp)
	movl	%ebx, 28(%esp)
	movl	%esi, 32(%esp)
	movl	%edi, 36(%esp)
	movl	%ebp, 40(%esp)
	leal	_self$, %ecx
	movl	%ecx, 0(%esp)
	call	_fun$main$reset
L100:
	movzbl	_a$, %ecx
	movzbl	_b$, %edx
	movzbl	_c$, %ebp
	movzbl	_d$, %esi
	leal	_self$, %ebx
	leal	56(%esp), %eax
	movl	%eax, 48(%esp)
	cmpl	$0, %ecx
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %edi
	cmpl	$0, %edx
	setne	%dl
	movzbl	%dl, %edx
	cmpl	$0, %ebp
	setne	%al
	movzbl	%al, %eax
	movl	%eax, %ebp
	cmpl	$0, %esi
	setne	%al
	movzbl	%al, %eax
	movl	%eax, 20(%esp)
	movl	%ebp, 16(%esp)
	movl	%edx, 12(%esp)
	movl	%edi, 8(%esp)
	movl	48(%esp), %ecx
	movl	%ecx, 4(%esp)
	movl	%ebx, 0(%esp)
	call	_fun$main$step
	movzbl	56(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _w$
	movzbl	57(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _x$
	movzbl	58(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _y$
	movzbl	59(%esp), %eax
	cmpl	$0, %eax
	setne	%al
	movzbl	%al, %eax
	movb	%al, _z$
	jmp	L100
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