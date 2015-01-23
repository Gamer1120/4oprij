package clientserver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

/**
 * ClientTUI program for the Connect4 according to the protocol of the TI-2
 * group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class ClientTUI implements ClientView {
	/**
	 * The Client this ClientTUI is made for.
	 */
	private Client client;
	/**
	 * The reader used to read from System.in.
	 */
	private BufferedReader reader;

	/**
	 * The InetAddress the ClientTUI will be connecting to.
	 */
	private InetAddress host;
	/**
	 * The port the ClientTUI will be connecting to.
	 */
	private int port;

	/**
	 * Creates a ClientTUI object.
	 */
	public ClientTUI() {
		this.reader = new BufferedReader(new InputStreamReader(System.in));
		setUpClient();
	}

	/**
	 * Prints a message to System.out.
	 * 
	 * @param msg
	 *            The message to print.
	 */
	public void addMessage(String msg) {
		System.out.println(msg);
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command.
	 */
	public void readInput() {
		while (true) {
			String input = null;
			String[] splitInput = null;
			try {
				input = reader.readLine();
				splitInput = input.split("\\s+");
			} catch (IOException | NullPointerException e) {
				client.shutdown();
				break;
			}
			switch (splitInput[0]) {
			case "QUIT":
				client.quit();
				break;
			case "HELP":
				client.help();
				break;
			case "MOVE":
				client.move(input, splitInput);
				break;
			case "INVITE":
				client.invite(input, splitInput);
				break;
			case "LEADERBOARD":
				client.sendMessage(Client.REQUEST_LEADERBOARD);
				break;
			case "DECLINE":
				client.decline(input, splitInput);
				break;
			default:
				//TODO: niet sturen?
				client.sendMessage(input);
				break;
			}
		}
	}

	/**
	 * The main method to start a new ClientTUI and connect to the Server.
	 * 
	 * @param args
	 *            The command line arguments.
	 */
	public static void main(String[] args) {
		new ClientTUI();
	}

	/**
	 * Asks the user for their name. If they enter -N or -S instead, a
	 * ComputerPlayer with a NaiveStrategy or SmartStrategy is made.
	 */
	/*
	 * while loop met boolean true totdat connect accept, client maken zonder player etc, in connect accept uiteindelijke naam opvragen en player maken
	 */
	@Override
	public void askName() {
		while (client.isConnected() == null || !client.isConnected()) {
			if (client.isConnected() == null) {
				addMessage("Please enter your name or -N or -S");
				try {
					client.setUpPlayer(reader.readLine());
				} catch (IOException e) {
					addMessage("[ERROR]Input disconnected. Shutting down.");
					System.exit(0);
				}
			}
		}
		readInput();
	}

	public InetAddress askHost() {
		InetAddress host = null;
		while (host == null) {
			addMessage("Please enter the IP address you'd like to connect to.");
			try {
				host = InetAddress.getByName(reader.readLine());
			} catch (UnknownHostException e) {
				addMessage("[ERROR]Unknown host.");
			} catch (IOException e) {
				addMessage("[ERROR]Input disconnected. Shutting down.");
				System.exit(0);
			}
		}
		return host;
	}

	public int askPort() {
		int port = 0;
		while (port == 0) {
			addMessage("Please enter the port you'd like to connect to.");
			try {
				port = (Integer.parseInt(reader.readLine()));
			} catch (NumberFormatException e) {
				addMessage("[ERROR]That is not a valid number.");
			} catch (IOException e) {
				addMessage("[ERROR]Input disconnected. Shutting down.");
				System.exit(0);
			}
		}
		return port;
	}

	public void setClient(Client client) {
		this.client = client;
	}

	private void setUpClient() {
		this.host = askHost();
		this.port = askPort();
		try {
			this.client = new Client(host, port, this);
		} catch (IOException e) {
			addMessage("[ERROR]Couldn't connect to the server.");
			setUpClient();
		}
		client.start();
		askName();
	}
}
