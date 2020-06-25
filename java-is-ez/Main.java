class Main {
    private static int a;
    private static long[] f0a = {8248156489741230770L, -5342668067454976247L, -889275714, -559038737};
    private static /* synthetic */ String[] f1a = {"redpwn", "ctf2020"};

    public static void main(String[] args) {
        if (args.length != 1) {
            System.exit(1);
        }
        if (args[0].length() != 32) {
            System.exit(1);
        }

        char[] arr = ("flag{" + args[0] + "}").toCharArray();
        int r3 = 0; //??
        int r1 = 1;
        int r4 = 0;
        // waste of time
        r1 = r1 - 1;
        char res = arr[r4];
        int result = r3 * 31 + res;
        r3 = result;
        r4++;

        int r7 = 0;
        int r5 = 0; // parsed long!
        //
        r3 = calc_sum("redpwn");
        long asdf = (r3 | (r3 << 32));
        long stat1 = f0a[r7];
        long stat2 = f0a[r7 + 2];
        long res1 = asdf ^ stat1;
        long res2 = r5 * stat2;
        assert res1 == res2;


        r4 = 0;
        try {
            Object r2 = args;
            Object r0 = 0;
            r0 = (Main) r0;
            java.util.concurrent.ThreadLocalRandom rand = java.util.concurrent.ThreadLocalRandom.current();
            a = rand.nextInt(1, 28);
            throw r2;
        } catch (Exception e) {
            r0 = e;
            r3 = r1;
            if (r0 == 0) goto L_0x0112
            int r0 = a
            int r1 = r3.length
            r2 = 1
            if (r1 != r2) goto L_0x00f8
        }


        r4 = 16;
        long r6 = java.lang.Long.parseLong(r2, r4);
        java.lang.String[] r2 = f1a;
        r2 = r2[r1];
        char[] r8 = r2.toCharArray();
        r5 = 0;
        if (r3 == 0) {
            r1 = r3[0];
            int r1 = r1.length();
            r2 = 32
            if (r1 != r2) {
                System.out.println("That is pepega");
                java.lang.System.exit(r1);
                if (r3 != 0) goto L_0x0070
                goto L_0x00d3
            }
        }
        r2 = 0;
        r4 = (long) r5;
        r2 = (() ^ f0a[r1]) > (r6 * f0a[r1 + 2]) ? 1 : (((r4 | (r4 << 32)) ^ f0a[r1]) == (r6 * f0a[r1 + 2]) ? 0 : -1));
    }
}