#!/usr/bin/env python3
ﰝ=True
𧡇=print
ࢴ=exit
𐰈=None
𞡂=False
𠜵=len
𓍇=format
𣞆=range
𐭤=hex
𞹡=chr
𐴐=isinstance
𞤢=list
𨡊=bytes
𐼹=int
𐲂=repr
ꕋ=ord
𡚾=id
ﮫ=open
import struct,sys
ﰬ=sys.argv
𠎮=sys.stdout
铸=sys.stdin
𨏲=struct.pack
𡬡=struct.unpack
import ctypes
𗭝=ctypes.addressof
𐠠=ctypes.c_void_p
얷=ctypes.c_int
ﺶ=ctypes.CFUNCTYPE
import mmap
𗒞=mmap.PROT_EXEC
𫂐=mmap.PROT_WRITE
ﲥ=mmap.PROT_READ
崵=mmap.PAGESIZE
瘥=mmap.mmap
𠄤={'value':0x01,'ax':0x11,'bx':0x12,'cx':0x13,'dx':0x14,'ip':0x21,'sp':0x22,'bp':0x23,'pointer':0x31,'ax pointer':0x41,'bx pointer':0x42,'cx pointer':0x43,'dx pointer':0x44,'ip pointer':0x51,'sp pointer':0x52,'bp pointer':0x53}
ޢ={'open':{'angstromctf':2,'cookie recipes':0x01,},'read':{'angstromctf':2,'cookie recipes':0x02,},}
𔔟={'del':{'angstromctf':1,'cookie recipes':0x01,},'osusec':{'angstromctf':1,'cookie recipes':0x02,},'perfect_blue':{'angstromctf':2,'cookie recipes':0x03,},'l_distribution':{'angstromctf':1,'cookie recipes':0x04,},'jmp':{'angstromctf':1,'cookie recipes':0x05,},'call':{'angstromctf':1,'cookie recipes':0x05,},'jle':{'angstromctf':1,'cookie recipes':0x06,},'b1c':{'angstromctf':1,'cookie recipes':0x07,},'jl':{'angstromctf':1,'cookie recipes':0x08,},'jg':{'angstromctf':1,'cookie recipes':0x09,},'mov':{'angstromctf':2,'cookie recipes':0x0c,},'gs_goofballs':{'angstromctf':2,'cookie recipes':0x0d,},'add':{'angstromctf':2,'cookie recipes':0x0e,},'sub':{'angstromctf':2,'cookie recipes':0x0f,},'end':{'angstromctf':1,'cookie recipes':0x10,},'kevin higgs <3':{'angstromctf':1,'cookie recipes':0x11,},'nop':{'angstromctf':0,'cookie recipes':0x12,},'load':{'angstromctf':2,'cookie recipes':0x13,},'dice_gang':{'angstromctf':2,'cookie recipes':0x14,},'rgbsec':{'angstromctf':0,'cookie recipes':0x15,},'%':{'angstromctf':0,'cookie recipes':0x25,}}
ﴀ=[0]*(2**(8*2))
try:
 𗚹=[3],[3],{2,3},[2]*3,[2,[2,{3,3,[3],{3}},{3:(2,[2,{3:(3,2,3,3)}],3)},2],2],3
except:
 pass
ﱏ={'ax':0,'bx':0,'cx':0,'dx':0,'ip':0,'sp':0,'bp':0,'flag':0}
𥋓=ﰝ
ﱖ=𧡇
𧡇=lambda*阬:ﱖ(*阬)if 𥋓 else ''
def ﷹ(reason):
 ﱖ('Bad memory condition')
 return ࢴ(1)
def ﶹ(start=0,end=𐰈,𓍇=𞡂,dump_ascii=ﰝ,errors='.'):
 if end is 𐰈:
  end=𠜵(ﴀ)
 if not 𓍇:
  pass
 else:
  𥓸=16
  for 𐴓 in 𣞆(start,end,𥓸):
   אּ=ﴀ[𐴓:𐴓+𥓸]
   𓇸=(𐭤(𐴓)+':').ljust(8,' ')+' '.join([𐭤(𩴽).replace('0x','').zfill(2)for 𩴽 in אּ])
   if dump_ascii:
    𓇸+='    '+''.join([(𞹡(𩴽)if 𩴽>31 and 𩴽<127 else errors)for 𩴽 in אּ])
def ܢ(value):
 return
def 儞(𐴓):
 if 𐴐(𐴓,𞤢):
  𐴓=𨡊(𐴓)
 return 𡬡('<H',𐴓)[0]
def 𠁻(value):
 if 𐴐(value,𐼹):
  return value
 𩊰,𨌋=value
 if 𩊰==𠄤['value']:
  return 𨌋
 if 𩊰==𠄤['ax']:
  return ﱏ['ax']
 if 𩊰==𠄤['bx']:
  return ﱏ['bx']
 if 𩊰==𠄤['cx']:
  return ﱏ['cx']
 if 𩊰==𠄤['dx']:
  return ﱏ['dx']
 if 𩊰==𠄤['ip']:
  return ﱏ['ip']
 if 𩊰==𠄤['sp']:
  return ﱏ['sp']
 if 𩊰==𠄤['bp']:
  return ﱏ['bp']
 if 𩊰==𠄤['pointer']:
  return 儞(ﴀ[𨌋:𨌋+2])
 return ﷹ('wrong_type')
def 𘑜(ނ,value):
 𥚒='\x00'
 if value>=256:
  𥚒=𨏲('<H',value)
 else:
  𥚒=𨡊([value])
 ނ=𠁻(ނ)
 𐴓=0
 for ࢮ in 𥚒:
  ﴀ[ނ+𐴓]=ࢮ
  𐴓+=1
def 𐠛(𢂥,count=2):
 𢂥=𠁻(𢂥)
 return ﴀ[𢂥:𢂥+count]
def 歚(殺,value):
 𩊰,𨌋=殺
 if 𩊰 in[𠄤['value'],𠄤['pointer']]:
  𘑜(𨌋,value)
 elif 𩊰==𠄤['ax']:
  ﱏ['ax']=value
 elif 𩊰==𠄤['bx']:
  ﱏ['bx']=value
 elif 𩊰==𠄤['cx']:
  ﱏ['cx']=value
 elif 𩊰==𠄤['dx']:
  ﱏ['dx']=value
 elif 𩊰==𠄤['ip']:
  ﱏ['ip']=value
 elif 𩊰==𠄤['sp']:
  ﱏ['sp']=value
 elif 𩊰==𠄤['bp']:
  ﱏ['bp']=value
def 𡍐(compiled):
 嶴=0
 for ࢮ in compiled:
  ﴀ[嶴]=ࢮ
  嶴+=1
 𐢇=儞(ﴀ[0:2])
 嶴+=16 
 ﱏ['ip']=𐢇
 ﱏ['bp']=嶴
 ﱏ['sp']=嶴
 while ﰝ:
  𐪎=ﴀ[ﱏ['ip']]
  ﭙ=𐰈
  ܢ('registers: '+𐲂(ﱏ))
  for ﳧ,instr in 𔔟.items():
   if 𐪎==instr['cookie recipes']:
    𐪎=instr
    ﭙ=ﳧ
    break
  if not ﭙ:
   ﷹ('invalid_instruction')
   return
  𥂬=𐪎['angstromctf']
  ܢ('instruction: '+𐲂(𐪎))
  阬=[]
  for 𩴽 in 𣞆(𥂬):
   殺=ﴀ[ﱏ['ip']+2+(4*𩴽):ﱏ['ip']+2+(4*𩴽)+4]
   𩱣=儞(殺[0:2])
   殺=儞(殺[2:4])
   阬.append((𩱣,殺))
  ﱏ['ip']+=2+(4*𥂬)
  ܢ('args: '+𐲂(阬))
  酩,篎,𪌠=1,2,3
  if ﭙ=='mov':
   歚(阬[0],𠁻(阬[1]))
  elif ﭙ=='add':
   歚(阬[0],𠁻(阬[0])+𠁻(阬[1]))
  elif ﭙ=='sub':
   歚(阬[0],𠁻(阬[0])-𠁻(阬[1]))
  elif ﭙ=='gs_goofballs':
   歚(阬[0],𠁻(阬[0])^𠁻(阬[1]))
  elif ﭙ=='nop':
   pass
  elif ﭙ=='perfect_blue':
   ℊ=𐼹(𠁻(阬[0]))
   ﶎ=𐼹(𠁻(阬[1]))
   if ℊ==ﶎ:
    ﱏ['flag']=酩
   if ℊ<ﶎ:
    ﱏ['flag']=篎
   if ℊ>ﶎ:
    ﱏ['flag']=𪌠
  elif ﭙ=='jmp':
   ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='jg':
   if ﱏ['flag']==𪌠:
    ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='jl':
   if ﱏ['flag']==篎:
    ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='l_distribution':
   if ﱏ['flag']==酩:
    ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='jle':
   if ﱏ['flag']in[篎,酩]:
    ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='b1c':
   if ﱏ['flag']in[𪌠,酩]:
    ﱏ['ip']=𠁻(阬[0])
  elif ﭙ=='del':
   𘑜(ﱏ['sp'],𠁻(阬[0]))
   ﱏ['sp']+=2 
  elif ﭙ=='osusec':
   歚(阬[0],儞(𐠛(ﱏ['sp'])))
   ﱏ['sp']-=2 
  elif ﭙ=='end':
   return(𠁻(阬[0]))
  elif ﭙ=='load':
   歚(阬[0],儞(𐠛(𠁻(阬[1]))))
  elif ﭙ=='dice_gang':
   𘑜(阬[0],𠁻(阬[1]))
  elif ﭙ=='kevin higgs <3':
   ﭱ=ﱏ['ax']
   𞤭=ﱏ['bx']
   𞢂=ﱏ['cx']
   if ﭱ==ޢ['open']['cookie recipes']:
    for 𐴓 in 𣞆(𞢂):
     ﴀ[𞤭+𐴓]=ꕋ(铸.read(1))
   elif ﭱ==ޢ['read']['cookie recipes']:
    𠎮.write(''.join([𞹡(𩴽)for 𩴽 in ﴀ[𞤭:𞤭+𞢂]]))
  elif ﭙ=='rgbsec':
   ࢴ()
  elif ﭙ=='%':
   ﳃ=𡚾(ﴀ[ﱏ['ip']:])+48
   𫉳=瘥(-1,崵,prot=ﲥ|𫂐|𗒞)
   𗼐=ﺶ(얷,얷)
   𓊭=𐠠.from_buffer(𫉳)
   𐲞=𗼐(𗭝(𓊭))
   𣩐=𨡊(ﴀ[ﱏ['ip']:]).replace(b'\x00',b'')
   𫉳.write(𣩐)
   ﻓ=𐲞(ﳃ)
   del 𓊭
   𫉳.close()
  for ﻦ,val in ﱏ.items():
   ﱏ[ﻦ]=val%0xffff
  ܢ('registers: '+𐲂(ﱏ))
  ܢ('-'*60)
 return
if __name__=='__main__':
 with ﮫ(ﰬ[1],'rb')as 𐲞:
  𐿰=𐲞.read()
  𡍐(𐿰)
