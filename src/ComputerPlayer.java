public class ComputerPlayer extends Player {
	private Strategy s;
	private Disc d;

	public ComputerPlayer(Disc disc, Strategy strategy) {
		super(strategy.getName() + "-Computer-" + disc, disc);
		s = strategy;
		d = disc;
	}

	public ComputerPlayer(Disc disc) {
		this(disc, new NaiveStrategy());
	}

	public Strategy getStrategy() {
		return s;
	}

	public void setStrategy(Strategy strategy) {
		s = strategy;
	}

	public int determineMove(Board b) {
		return s.determineMove(b, d);
	}
}
