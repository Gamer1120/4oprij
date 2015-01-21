package game;

/**
 * SmartStrategy for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
import java.util.HashSet;
import java.util.Set;

public class SmartStrategy implements Strategy {
	public final static String NAME = "Smart";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		Set<Integer> empty = new HashSet<Integer>();
		for (int i = 0; i < b.getColumns(); i++) {
			if (b.isEmptyField(i)) {
				empty.add(i);
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d);
			if (board.gameOver()) {
				return i;
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d.other());
			if (board.gameOver()) {
				return i;
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d);
			for (Integer j : empty) {
				board.insertDisc(j, d);
				if (board.gameOver()) {
					return j;
				}
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d.other());
			for (Integer j : empty) {
				board.insertDisc(j, d.other());
				if (board.gameOver()) {
					return j;
				}
			}
		}
		return (int) empty.toArray()[((int) (Math.random() * empty.size()))];
	}

	//TODO: Implement a canWin(Board b, Disc d) method, which is mainly copy-pasta.
}
