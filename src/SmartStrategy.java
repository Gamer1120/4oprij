import java.util.HashSet;
import java.util.Set;

public class SmartStrategy implements Strategy {
	public final static String NAME = "Smart";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		Set<Integer> empty = new HashSet<Integer>();
		for (int i = 0; i < Board.HORIZONTAL; i++) {
			if (b.isEmptyField(i)) {
				empty.add(i);
			}
		}
		if (empty.contains(Board.HORIZONTAL / 2)) {
			return Board.HORIZONTAL / 2;
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
		return (int) empty.toArray()[((int) (Math.random() * empty.size()))];
	}
	
	//TODO: Implement a canWin(Board b, Disc d) method, which is mainly copy-pasta.
}
