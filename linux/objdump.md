# objdump & readelf

These two commands are used to display information from object files.

    objdump -s ./a.out # -s --full-contents. display all sections
    objdump -d ./a.out # disassemble
    objdump -ds ./a.out # display both instructions and data.
    objdump -dj .text ./a.out # disassemble parts containing code
    objdump -sj .rodata ./a.out # display .rodata section
    readelf -x .rodata ./a.out # display .rodata section


