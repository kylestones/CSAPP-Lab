movl %esp,%eax
movl %eax,%edx
movl %edx, %ecx
movl %ecx,%esi
popq %rax
movl %eax,%edi
lea  (%edi,%esi,1),%rax
movl %eax,%edi
