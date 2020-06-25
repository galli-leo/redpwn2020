package defpackage;

/* renamed from: JavaIsEZ2  reason: default package */
/* compiled from: RedpwnCTF2020 */
public class JavaIsEZ2 {
    private static /* synthetic */ int a;

    /* renamed from: a  reason: collision with other field name */
    private static /* synthetic */ long[] f0a = {8248156489741230770L, -5342668067454976247L, -889275714, -559038737};

    /* renamed from: a  reason: collision with other field name */
    private static /* synthetic */ String[] f1a = {"redpwn", "ctf2020"};

    /* JADX WARNING: Code restructure failed: missing block: B:10:?, code lost:
        throw null;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:11:0x001c, code lost:
        r0 = th;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:123:?, code lost:
        return;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:14:0x0023, code lost:
        if (r3.length == 1) goto L_0x0025;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:15:0x0025, code lost:
        if (r0 != 0) goto L_0x001a;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:16:0x0027, code lost:
        r0 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:18:0x0031, code lost:
        if (r3[0].length() != 32) goto L_0x00f8;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:19:0x0033, code lost:
        if (r0 == 0) goto L_0x0112;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:20:0x0035, code lost:
        r0 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:21:0x0036, code lost:
        r5 = ("flag{" + r3[0] + "}").toCharArray();
        r4 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:22:0x0057, code lost:
        if (r3 == null) goto L_0x0028;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:23:0x0059, code lost:
        r1 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:25:0x0060, code lost:
        if (r1 == (-((r5.length ^ -1) + 2))) goto L_0x00d4;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:26:0x0062, code lost:
        monitor-enter(r5);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:27:0x0063, code lost:
        if (r1 < 0) goto L_0x0070;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:28:0x0065, code lost:
        r1 = r1 + 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:30:0x006b, code lost:
        if (r4 != 1140336659) goto L_0x00f8;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:31:0x006d, code lost:
        if (r0 != 0) goto L_0x001a;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:32:0x006f, code lost:
        r0 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:33:0x0070, code lost:
        r1 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:34:0x0071, code lost:
        r2 = r3[0];
     */
    /* JADX WARNING: Code restructure failed: missing block: B:35:0x0074, code lost:
        if (r1 != 0) goto L_0x009d;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:36:0x0076, code lost:
        r2 = r2.substring(0, 16);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:37:0x007d, code lost:
        r6 = java.lang.Long.parseLong(r2, 16);
        r8 = f1a[r1].toCharArray();
        r5 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:38:0x008c, code lost:
        if (r3 == null) goto L_0x0028;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:39:0x008e, code lost:
        r2 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:41:0x0095, code lost:
        if (r2 == (-((r8.length ^ -1) + 2))) goto L_0x00e6;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:42:0x0097, code lost:
        monitor-enter(r8);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:43:0x0098, code lost:
        if (r2 < 0) goto L_0x0070;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:44:0x009a, code lost:
        r2 = r2 + 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:45:0x009d, code lost:
        r2 = r2.substring(16);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:46:0x00a4, code lost:
        r4 = (long) r5;
        r2 = (((r4 | (r4 << 32)) ^ f0a[r1]) > (r6 * f0a[r1 + 2]) ? 1 : (((r4 | (r4 << 32)) ^ f0a[r1]) == (r6 * f0a[r1 + 2]) ? 0 : -1));
     */
    /* JADX WARNING: Code restructure failed: missing block: B:47:0x00b8, code lost:
        switch(r0) {
            case 2: goto L_0x00c2;
            case 3: goto L_0x0025;
            case 10: goto L_0x006d;
            case 12: goto L_0x0112;
            case 16: goto L_0x00c0;
            case 20: goto L_0x0070;
            case 21: goto L_0x00c5;
            case 29: goto L_0x00bd;
            case 30: goto L_0x0036;
            case 50: goto L_0x00c8;
            case 54: goto L_0x0028;
            case 55: goto L_0x0033;
            case 66: goto L_0x001a;
            default: goto L_0x00bb;
        };
     */
    /* JADX WARNING: Code restructure failed: missing block: B:48:0x00bb, code lost:
        if (r2 != 0) goto L_0x00f8;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:49:0x00bd, code lost:
        if (r0 == 0) goto L_0x001a;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:50:0x00bf, code lost:
        r0 = 0;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:51:0x00c0, code lost:
        r1 = r1 + 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:52:0x00c2, code lost:
        if (r0 != 0) goto L_0x001a;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:53:0x00c4, code lost:
        r0 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:55:0x00c6, code lost:
        if (2 != r1) goto L_0x0071;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:57:0x00d4, code lost:
        r2 = 0;
        r1 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:58:0x00d6, code lost:
        if (r1 == 0) goto L_0x0068;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:59:0x00d8, code lost:
        r1 = r1 - 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:61:?, code lost:
        r4 = r5[r2] + (r4 * 31);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:62:0x00df, code lost:
        monitor-exit(r5);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:63:0x00e0, code lost:
        r2 = r2 + 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:64:0x00e2, code lost:
        if (r1 < 0) goto L_0x0112;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:65:0x00e4, code lost:
        r1 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:66:0x00e6, code lost:
        r4 = 0;
        r2 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:67:0x00e8, code lost:
        if (r2 == 0) goto L_0x00a4;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:68:0x00ea, code lost:
        r2 = r2 - 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:70:?, code lost:
        r5 = r8[r4] + (r5 * 31);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:71:0x00f1, code lost:
        monitor-exit(r8);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:72:0x00f2, code lost:
        r4 = r4 + 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:73:0x00f4, code lost:
        if (r2 < 0) goto L_0x0112;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:74:0x00f6, code lost:
        r2 = 1;
     */
    /* JADX WARNING: Code restructure failed: missing block: B:75:0x00f8, code lost:
        java.lang.System.out.println("That is pepega");
        java.lang.System.exit(0);
     */
    /* JADX WARNING: Code restructure failed: missing block: B:76:0x0103, code lost:
        if (r3 != null) goto L_0x0070;
     */
    /* JADX WARNING: Removed duplicated region for block: B:13:0x001f  */
    /* Code decompiled incorrectly, please refer to instructions dump. */
    public static /* bridge */ /* synthetic */ void main(java.lang.String[] r10) {
        /*
            r2 = r10
        L_0x0001:
            r0 = 0
            RedpwnCTF2020 r0 = (RedpwnCTF2020) r0     // Catch:{ all -> 0x010a }
            java.lang.String r0 = "java.utils.ArrayList"
            java.lang.Class.forName(r0)     // Catch:{ all -> 0x010a }
            java.util.concurrent.ThreadLocalRandom r0 = java.util.concurrent.ThreadLocalRandom.current()     // Catch:{ all -> 0x010a }
            r1 = 1
            r3 = 28
            int r0 = r0.nextInt(r1, r3)     // Catch:{ all -> 0x010a }
            a = r0     // Catch:{ all -> 0x010a }
            r1 = 0
            monitor-exit(r2)     // Catch:{ all -> 0x010e }
            r2 = r1
            goto L_0x0001
        L_0x001a:
            r0 = 0
            throw r0     // Catch:{ all -> 0x001c }
        L_0x001c:
            r0 = move-exception
        L_0x001d:
            if (r0 == 0) goto L_0x0112
            int r0 = a
            int r1 = r3.length
            r2 = 1
            if (r1 != r2) goto L_0x00f8
        L_0x0025:
            if (r0 != 0) goto L_0x001a
            r0 = 1
        L_0x0028:
            r1 = 0
            r1 = r3[r1]
            int r1 = r1.length()
            r2 = 32
            if (r1 != r2) goto L_0x00f8
        L_0x0033:
            if (r0 == 0) goto L_0x0112
            r0 = 0
        L_0x0036:
            java.lang.StringBuilder r1 = new java.lang.StringBuilder
            r1.<init>()
            java.lang.String r2 = "flag{"
            java.lang.StringBuilder r1 = r1.append(r2)
            r2 = 0
            r2 = r3[r2]
            java.lang.StringBuilder r1 = r1.append(r2)
            java.lang.String r2 = "}"
            java.lang.StringBuilder r1 = r1.append(r2)
            java.lang.String r1 = r1.toString()
            char[] r5 = r1.toCharArray()
            r4 = 0
            if (r3 == 0) goto L_0x0028
            r1 = 0
        L_0x005a:
            int r2 = r5.length
            r2 = r2 ^ -1
            int r2 = r2 + 2
            int r2 = -r2
            if (r1 == r2) goto L_0x00d4
            monitor-enter(r5)
            if (r1 < 0) goto L_0x0070
            int r1 = r1 + 1
            goto L_0x005a
        L_0x0068:
            r1 = 1140336659(0x43f82813, float:496.31308)
            if (r4 != r1) goto L_0x00f8
        L_0x006d:
            if (r0 != 0) goto L_0x001a
            r0 = 1
        L_0x0070:
            r1 = 0
        L_0x0071:
            r2 = 0
            r2 = r3[r2]
            if (r1 != 0) goto L_0x009d
            r4 = 0
            r5 = 16
            java.lang.String r2 = r2.substring(r4, r5)
        L_0x007d:
            r4 = 16
            long r6 = java.lang.Long.parseLong(r2, r4)
            java.lang.String[] r2 = f1a
            r2 = r2[r1]
            char[] r8 = r2.toCharArray()
            r5 = 0
            if (r3 == 0) goto L_0x0028
            r2 = 0
        L_0x008f:
            int r4 = r8.length
            r4 = r4 ^ -1
            int r4 = r4 + 2
            int r4 = -r4
            if (r2 == r4) goto L_0x00e6
            monitor-enter(r8)
            if (r2 < 0) goto L_0x0070
            int r2 = r2 + 1
            goto L_0x008f
        L_0x009d:
            r4 = 16
            java.lang.String r2 = r2.substring(r4)
            goto L_0x007d
        L_0x00a4:
            long r4 = (long) r5
            r2 = 32
            long r8 = r4 << r2
            long r4 = r4 | r8
            long[] r2 = f0a
            r8 = r2[r1]
            long r4 = r4 ^ r8
            long[] r2 = f0a
            int r8 = r1 + 2
            r8 = r2[r8]
            long r6 = r6 * r8
            int r2 = (r4 > r6 ? 1 : (r4 == r6 ? 0 : -1))
            switch(r0) {
                case 2: goto L_0x00c2;
                case 3: goto L_0x0025;
                case 10: goto L_0x006d;
                case 12: goto L_0x0112;
                case 16: goto L_0x00c0;
                case 20: goto L_0x0070;
                case 21: goto L_0x00c5;
                case 29: goto L_0x00bd;
                case 30: goto L_0x0036;
                case 50: goto L_0x00c8;
                case 54: goto L_0x0028;
                case 55: goto L_0x0033;
                case 66: goto L_0x001a;
                default: goto L_0x00bb;
            }
        L_0x00bb:
            if (r2 != 0) goto L_0x00f8
        L_0x00bd:
            if (r0 == 0) goto L_0x001a
            r0 = 0
        L_0x00c0:
            int r1 = r1 + 1
        L_0x00c2:
            if (r0 != 0) goto L_0x001a
            r0 = 1
        L_0x00c5:
            r2 = 2
            if (r2 != r1) goto L_0x0071
        L_0x00c8:
            r0 = 0
            java.io.PrintStream r1 = java.lang.System.out
            java.lang.String r2 = "Oh nice, you found my key :O"
            r1.println(r2)
            java.lang.System.exit(r0)
        L_0x00d3:
            return
        L_0x00d4:
            r2 = 0
            r1 = 1
        L_0x00d6:
            if (r1 == 0) goto L_0x0068
            int r1 = r1 + -1
            int r6 = r4 * 31
            char r4 = r5[r2]     // Catch:{ IllegalMonitorStateException -> 0x0108 }
            int r4 = r4 + r6
            monitor-exit(r5)     // Catch:{ IllegalMonitorStateException -> 0x0108 }
            int r2 = r2 + 1
            if (r1 < 0) goto L_0x0112
            r1 = 1
            goto L_0x00d6
        L_0x00e6:
            r4 = 0
            r2 = 1
        L_0x00e8:
            if (r2 == 0) goto L_0x00a4
            int r2 = r2 + -1
            int r9 = r5 * 31
            char r5 = r8[r4]     // Catch:{ IllegalMonitorStateException -> 0x0106 }
            int r5 = r5 + r9
            monitor-exit(r8)     // Catch:{ IllegalMonitorStateException -> 0x0106 }
            int r4 = r4 + 1
            if (r2 < 0) goto L_0x0112
            r2 = 1
            goto L_0x00e8
        L_0x00f8:
            r1 = 0
            java.io.PrintStream r2 = java.lang.System.out
            java.lang.String r4 = "That is pepega"
            r2.println(r4)
            java.lang.System.exit(r1)
            if (r3 != 0) goto L_0x0070
            goto L_0x00d3
        L_0x0106:
            r9 = move-exception
            goto L_0x00e8
        L_0x0108:
            r6 = move-exception
            goto L_0x00d6
        L_0x010a:
            r0 = move-exception
            r3 = r2
            goto L_0x001d
        L_0x010e:
            r0 = move-exception
            r3 = r1
            goto L_0x001d
        L_0x0112:
            r2 = r3
            goto L_0x0001
        */
        throw new UnsupportedOperationException("Method not decompiled: defpackage.JavaIsEZ2.main(java.lang.String[]):void");
    }

    public static long print(long j) {
        System.out.println(j);
        return j;
    }
}
