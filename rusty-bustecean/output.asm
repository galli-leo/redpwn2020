0x0000:		PUSH_IMM 0x8
0x0010:		POP rax
0x0020:		READ rbx
0x0030:		OR rcx, rbx
0x0040:		SHL rcx, rax
0x0050:		READ rbx
0x0060:		OR rcx, rbx
0x0070:		SHL rcx, rax
0x0080:		READ rbx
0x0090:		OR rcx, rbx
0x00a0:		SHL rcx, rax
0x00b0:		READ rbx
0x00c0:		OR rcx, rbx
0x00d0:		PUSH_IMM 0xaa551337
0x00e0:		POP rdx
0x00f0:		XOR rcx, rdx
0x0100:		PUSH_IMM 0xcc397250
0x0110:		POP rax
0x0120:		NE_SKIP rax, rcx
0x0130:		FAR_JMP 0x210
0x0140:		PUSH_IMM 0x4c
0x0150:		POP rax
0x0160:		WRITE rax
0x0170:		PUSH_IMM 0x6f
0x0180:		POP rax
0x0190:		WRITE rax
0x01a0:		PUSH_IMM 0x73
0x01b0:		POP rax
0x01c0:		WRITE rax
0x01d0:		PUSH_IMM 0x65
0x01e0:		POP rax
0x01f0:		WRITE rax
0x0200:		DONE uk
0x0210:		PUSH_IMM 0x4444
0x0220:		POP rax
0x0230:		PUSH_IMM 0x3759
0x0240:		POP rbx
0x0250:		PUSH_IMM 0x7
0x0260:		POP rbx
0x0270:		IMUL rax, rbx
0x0280:		OR rax, rbx
0x0290:		PUSH_IMM 0x3
0x02a0:		POP rbx
0x02b0:		SHR rax, rbx
0x02c0:		READ rbx
0x02d0:		PUSH_IMM 0x8
0x02e0:		POP rcx
0x02f0:		SHL rbx, rcx
0x0300:		READ rdx
0x0310:		OR rbx, rdx
0x0320:		PUSH_IMM 0x40cc
0x0330:		POP rcx
0x0340:		XOR rbx, rcx
0x0350:		NE_SKIP rax, rbx
0x0360:		NEAR_JMP 0x380
0x0370:		FAR_JMP 0x140
0x0380:		PUSH_IMM 0x8
0x0390:		POP rax
0x03a0:		PUSH_IMM 0x0
0x03b0:		READ rbx
0x03c0:		POP rcx
0x03d0:		OR rcx, rbx
0x03e0:		SHL rcx, rax
0x03f0:		READ rbx
0x0400:		OR rcx, rbx
0x0410:		SHL rcx, rax
0x0420:		READ rbx
0x0430:		OR rcx, rbx
0x0440:		SHL rcx, rax
0x0450:		READ rbx
0x0460:		OR rcx, rbx
0x0470:		SHL rcx, rax
0x0480:		READ rbx
0x0490:		OR rcx, rbx
0x04a0:		SHL rcx, rax
0x04b0:		READ rbx
0x04c0:		OR rcx, rbx
0x04d0:		PUSH_REG rcx
0x04e0:		POP rdx
0x04f0:		PUSH_IMM 0x561245
0x0500:		POP rbx
0x0510:		IMUL rbx, rip
0x0520:		SHL rbx, rax
0x0530:		OR rbx, rax
0x0540:		XOR rbx, rip
0x0550:		PUSH_IMM 0x233
0x0560:		POP rax
0x0570:		IMUL rbx, rax
0x0580:		MOV_MEM rcx, [rcx - rbx]
0x0590:		XOR rcx, rdx
0x05a0:		PUSH_IMM 0x3544
0x05b0:		PUSH_IMM 0x1475eafc5
0x05c0:		POP rax
0x05d0:		POP rbx
0x05e0:		IMUL rax, rbx
0x05f0:		NE_SKIP rax, rcx
0x0600:		NEAR_JMP 0x620
0x0610:		FAR_JMP 0x140
0x0620:		ADD rcx, rdx
0x0630:		IMUL rcx, rbx
0x0640:		PUSH_REG rcx
0x0650:		POP rdx
0x0660:		PUSH_IMM 0x8
0x0670:		POP rax
0x0680:		PUSH_IMM 0x0
0x0690:		READ rbx
0x06a0:		POP rcx
0x06b0:		OR rcx, rbx
0x06c0:		SHL rcx, rax
0x06d0:		READ rbx
0x06e0:		OR rcx, rbx
0x06f0:		SHL rcx, rax
0x0700:		READ rbx
0x0710:		OR rcx, rbx
0x0720:		SHL rcx, rax
0x0730:		READ rbx
0x0740:		OR rcx, rbx
0x0750:		SHL rcx, rax
0x0760:		READ rbx
0x0770:		OR rcx, rbx
0x0780:		SHL rcx, rax
0x0790:		READ rbx
0x07a0:		OR rcx, rbx
0x07b0:		SHL rcx, rax
0x07c0:		READ rbx
0x07d0:		OR rcx, rbx
0x07e0:		SHL rcx, rax
0x07f0:		READ rbx
0x0800:		OR rcx, rbx
0x0810:		XOR rdx, rcx
0x0820:		PUSH_REG rdx
0x0830:		PUSH_IMM 0xeddd428674d7
0x0840:		POP rbx
0x0850:		PUSH_REG rbx
0x0860:		POP rdx
0x0870:		PUSH_IMM 0x5143
0x0880:		POP rax
0x0890:		PUSH_IMM 0x1
0x08a0:		POP rcx
0x08b0:		NE_SKIP rax, rcx
0x08c0:		FAR_JMP 0x940
0x08d0:		ADD rbx, rdx
0x08e0:		PUSH_REG rax
0x08f0:		PUSH_IMM 0x1
0x0900:		POP rax
0x0910:		ADD rcx, rax
0x0920:		POP rax
0x0930:		FAR_JMP 0x8b0
0x0940:		POP rdx
0x0950:		NE_SKIP rbx, rdx
0x0960:		NEAR_JMP 0x980
0x0970:		FAR_JMP 0x140
0x0980:		PUSH_IMM 0x8
0x0990:		POP rax
0x09a0:		PUSH_IMM 0x0
0x09b0:		READ rbx
0x09c0:		POP rcx
0x09d0:		OR rcx, rbx
0x09e0:		SHL rcx, rax
0x09f0:		READ rbx
0x0a00:		OR rcx, rbx
0x0a10:		SHL rcx, rax
0x0a20:		READ rbx
0x0a30:		OR rcx, rbx
0x0a40:		SHL rcx, rax
0x0a50:		READ rbx
0x0a60:		OR rcx, rbx
0x0a70:		SHL rcx, rax
0x0a80:		READ rbx
0x0a90:		OR rcx, rbx
0x0aa0:		PUSH_IMM 0x7fffffffff
0x0ab0:		POP rdx
0x0ac0:		AND rcx, rdx
0x0ad0:		ADD rdx, rcx
0x0ae0:		PUSH_IMM 0xf2656e6364
0x0af0:		POP rbx
0x0b00:		NE_SKIP rbx, rdx
0x0b10:		NEAR_JMP 0xb30
0x0b20:		FAR_JMP 0x140
0x0b30:		PUSH_IMM 0x0
0x0b40:		POP rcx
0x0b50:		READ rbx
0x0b60:		XOR rcx, rbx
0x0b70:		READ rbx
0x0b80:		NE_SKIP rcx, rbx
0x0b90:		NEAR_JMP 0xbb0
0x0ba0:		FAR_JMP 0x140
0x0bb0:		READ rcx
0x0bc0:		NE_SKIP rcx, rbx
0x0bd0:		NEAR_JMP 0xbf0
0x0be0:		FAR_JMP 0x140
0x0bf0:		PUSH_IMM 0x2e
0x0c00:		READ rax
0x0c10:		PUSH_IMM 0x8
0x0c20:		POP rdx
0x0c30:		SHL rax, rdx
0x0c40:		ADD rax, rcx
0x0c50:		PUSH_IMM 0x7d2e
0x0c60:		POP rbx
0x0c70:		NE_SKIP rax, rbx
0x0c80:		NEAR_JMP 0xca0
0x0c90:		FAR_JMP 0x140
0x0ca0:		PUSH_IMM 0x57
0x0cb0:		POP rax
0x0cc0:		WRITE rax
0x0cd0:		PUSH_IMM 0x69
0x0ce0:		POP rax
0x0cf0:		WRITE rax
0x0d00:		PUSH_IMM 0x6e
0x0d10:		POP rax
0x0d20:		WRITE rax
0x0d30:		DONE uk
