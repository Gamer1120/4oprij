public class Connect4 {
	public final static String NAIVE_PLAYER = "-N";
	public final static String SMART_PLAYER = "-S";

	public static void main(String[] args) {
		Player[] player = new Player[Game.NUMBER_PLAYERS];
		GameView view = null;
		Disc d = Disc.YELLOW;
		for (int i = 0; i < Game.NUMBER_PLAYERS; i++) {
			if (i >= args.length) {
				player[i] = new ComputerPlayer(d);
			} else if (NAIVE_PLAYER.equalsIgnoreCase(args[i])) {
				player[i] = new ComputerPlayer(d, new NaiveStrategy());
			} else if (SMART_PLAYER.equalsIgnoreCase(args[i])) {
				player[i] = new ComputerPlayer(d, new SmartStrategy());
			} else {
				player[i] = new HumanPlayer(args[i], d, view);
			}
			d = d.other();
		}
		Game game = new Game(player[0], player[1], view);
		game.start();
	}
	//TODO: argumenten voor view toevoegen
}
