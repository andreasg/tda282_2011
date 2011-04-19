import java.util.Scanner;

class Runtime {
    private static Scanner in = new Scanner(System.in);
    
    public static void printInt(int i) {
        System.out.println(i);
    }

    public static void printDouble(double d) {
        System.out.println(d);
    }

    public static void printString(String s) {
        System.out.println(s);
    }

    public static int readInt() {
        int i = in.nextInt();
        return i;
    }

    public static double readDouble() {
        return in.nextDouble();
    }
}