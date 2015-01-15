package game;
public class Test {
	public final static int N = 0;
	public final static Disc D = Disc.YELLOW;

	/**
	 * This is a test method, mainly designed for testing purposes.
	 */
	public static void main(String[] args) {
		Board board = new Board();
		printAll(board);
	}

	public static void printAll(Board b) {
		System.out.println(b);
		System.out.println(b.deepCopy());
		System.out.println(b.emptyRow(N));
		System.out.println(b.fullRow(N));
		System.out.println(b.isField(N));
		System.out.println(b.isField(N, N));
		System.out.println(b.getField(N, N));
		System.out.println(b.isEmptyField(N, N));
		System.out.println(b.isFull());
		System.out.println(b.gameOver());
		System.out.println(b.hasRow(D));
		System.out.println(b.hasColumn(D));
		System.out.println(b.hasDiagonal(D));
		System.out.println(b.isWinner(D));
		System.out.println(b.hasWinner());
		System.out.println(b.toString());
		b.insertDisc(N, D);
		System.out.println(b);
		b.setField(N, N, D);
		System.out.println(b);
		b.reset();
		System.out.println(b);
	}
}
