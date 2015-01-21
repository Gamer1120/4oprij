package game;

import clientserver.ClientView;

/**
 * Class for maintaining a HumanPlayer in Connect4.
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class HumanPlayer extends Player {
	/**
	 * The View used by the Client
	 */
	private ClientView view;

	//@ private invariant view != null;

	/**
	 * Creates a new HumanPlayer object with a given Disc and ClientView.
	 * 
	 * @param disc
	 *            The Disc this HumanPlayer should have.
	 * @param viewArg
	 *            The ClientView this HumanPlayer should have.
	 */
	/*@
		requires disc == Disc.YELLOW || disc == Disc.RED;
		requires viewArg != null;
		ensures getDisc() == disc;
	 */
	public HumanPlayer(Disc disc, ClientView viewArg) {
		super("HumanPlayer", disc);
		view = viewArg;
	}

	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the view.
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	/*@
		requires board != null;
		ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	public int determineMove(Board board) {
		return view.makeMove();
	}
}
